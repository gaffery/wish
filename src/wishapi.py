import os
import re
import sys
import time
import uuid
import shutil
import socket
import sqlite3
import threading
import subprocess
import urllib.parse
from functools import lru_cache

import minio
import requests


class Locker(object):
    def __init__(self):
        self._locks = dict()
        self._lock = threading.Lock()

    def _get_lock_file(self, base_path, tags, action):
        return os.path.join(base_path, ".{}.{}.lock".format(tags, action))

    def __enter__(self):
        lock_dir = os.path.dirname(self.lock_path)
        if not os.path.exists(lock_dir):
            os.makedirs(lock_dir, exist_ok=True)

        start_time = time.time()
        max_wait_time = 10
        wait_time = 1

        while True:
            try:
                with self._lock:
                    if self.lock_path not in self._locks:
                        fd = os.open(self.lock_path, os.O_CREAT | os.O_EXCL | os.O_RDWR)
                        self._locks[self.lock_path] = fd
                        return self
            except FileExistsError:
                if time.time() - start_time > self.timeout:
                    try:
                        os.remove(self.lock_path)
                    except Exception:
                        pass
                sys.stdout.write(
                    "[{} {}] Progress: Wait {:.0f}s for {}...\r".format(
                        self.name, self.tags, time.time() - start_time, self.action
                    )
                )
                sys.stdout.flush()
                time.sleep(wait_time)
                wait_time = min(wait_time * 2, max_wait_time)

    def __exit__(self, *_):
        with self._lock:
            if self.lock_path in self._locks:
                try:
                    os.close(self._locks[self.lock_path])
                    os.remove(self.lock_path)
                except Exception:
                    pass
                del self._locks[self.lock_path]

    def start(self, base_path, tags, action, timeout=60):
        self.lock_path = self._get_lock_file(base_path, tags, action)
        self.tags = tags
        self.action = action
        self.timeout = timeout
        self.name = os.path.basename(base_path)
        return self


class Loader(object):
    def __init__(self, **kwargs):
        self.start_time = 0
        self.object_name = str()
        self.last_output_time = 0
        self.output_interval = 0.5
        self.total_bytes = 0
        self.sync_bytes = 0
        self.kwargs = kwargs
        self.action = kwargs.get("action")

    def set_meta(self, object_name, total_length):
        self.start_time = time.time()
        self.object_name = object_name
        self.total_bytes = total_length
        self.last_output_time = self.start_time

    def update(self, sync_bytes):
        self.sync_bytes += sync_bytes
        current_time = time.time()
        elapsed_time = current_time - self.start_time
        if (
            self.sync_bytes == self.total_bytes
            or current_time - self.last_output_time >= self.output_interval
        ):
            progress = (self.sync_bytes / self.total_bytes) * 100
            if elapsed_time == 0:
                speed = 0
            else:
                speed = self.sync_bytes / elapsed_time
            speed_display = self._format_bytes(speed) + "/s"
            total_display = self._format_bytes(self.total_bytes)
            info_str = "[{} {}] Progress: {:.0f}% {}: {} Speed: {}\r".format(
                self.kwargs.get("name"),
                self.kwargs.get("tags"),
                progress,
                self.action,
                total_display,
                speed_display,
            )
            if progress == 100:
                info_str = "\r" + info_str[0:-1] + "\n"
            sys.stdout.write(info_str)
            sys.stdout.flush()
            self.last_output_time = current_time

    def _format_bytes(self, byte):
        if byte > 1024**2:
            return "{:.2f}MB".format(byte / 1024**2)
        elif byte > 1024:
            return "{:.2f}KB".format(byte / 1024)
        else:
            return "{:.2f}B".format(byte)


class Packer(object):
    def __init__(self, **kwargs):
        self.last_output_time = 0
        self.output_interval = 0.5
        self.tilte = "[{} {}] Progress: ".format(kwargs.get("name"), kwargs.get("tags"))

    def unpack(self, archive_pkg, output_dir):
        self.action = "Unpacking"
        cmd_str = "7z x {} -tzip -bsp1 -aoa -o{}".format(archive_pkg, output_dir)
        process = subprocess.Popen(
            cmd_str,
            shell=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        thread = threading.Thread(target=self._read_output, args=(process.stdout,))
        thread.start()
        process.wait()
        thread.join()
        process.kill()

    def pack(self, archive_dir, output_pkg):
        self.action = "Packing"
        cmd_str = "7z a {} {}/* -tzip".format(output_pkg, archive_dir)
        process = subprocess.Popen(
            cmd_str,
            shell=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        thread = threading.Thread(target=self._read_output, args=(process.stdout,))
        thread.start()
        process.wait()
        thread.join()
        process.kill()

    def _read_output(self, stream):
        new_line = list()
        current_line = list()
        for char in iter(lambda: stream.read(1), str()):
            if char == "\b":
                if current_line:
                    new_line.insert(0, current_line.pop())
                    if not current_line:
                        self._parse_output("".join(new_line).strip())
                        new_line = list()
            elif char == "\r":
                self._parse_output("".join(current_line).strip())
                current_line = list()
            elif char == "\n":
                self._parse_output("".join(current_line).strip())
                current_line = list()
            else:
                current_line.append(char)

    def _parse_output(self, line):
        current_time = time.time()
        progress_regex = re.compile(r"^\d+%\s+.*")
        if progress_regex.match(line):
            linelist = line.split(" - ")[0].split()
            progress = linelist[0]
            filecount = linelist[1]
            if current_time - self.last_output_time >= self.output_interval:
                stdout_str = "\r{}{} {}: {}\r".format(
                    self.tilte, progress, self.action, filecount
                )
                sys.stdout.write(stdout_str)
                self.last_output_time = current_time
        if line.startswith("Files:"):
            progress = "100%"
            filecount = line.split(":")[-1]
            stdout_str = "\r{}{} {}: {}\n".format(
                self.tilte, progress, self.action, filecount
            )
            sys.stdout.write(stdout_str)
        sys.stdout.flush()


class Client(object):
    __message = True

    def __init__(self, url, config=None, environ=None):
        super(Client, self).__init__()
        self.environ = environ
        self.config = config
        self.client = None
        self.logged = True
        if not url:
            self._message("Url not exist")
            self.logged = False
            return
        if self.environ(self.config.Env.PACKAGE_MODE).getenv() == "1":
            self._message("Switch to local mode")
            self.logged = False
            return
        self.parsed_url(url)
        if not self.check_net(self.host, self.port):
            self._message("Network unavailable fallback to local mode")
            self.logged = False
            return

    def _message(self, message):
        if self.config.VERBOSE == "+" and Client.__message:
            sys.stdout.write("Extra Info: {}\n".format(message))
            sys.stdout.flush()
        Client.__message = False

    def check_net(self, host, port):
        port = int(port)
        timeout = 0.5
        try:
            socket.setdefaulttimeout(timeout)
            socket.socket(socket.AF_INET, socket.SOCK_STREAM).connect((host, port))
            return True
        except Exception:
            return False

    def parsed_url(self, url):
        url = url.strip('"')
        parse = urllib.parse.urlparse(url)
        query_params = urllib.parse.parse_qs(parse.query)
        self.host, self.port = parse.netloc.split(":")
        self.netloc = parse.netloc
        if not self.port:
            self.port = "80"
        if parse.scheme == "http":
            self.secure = False
        else:
            self.secure = True
        self.scheme = parse.scheme
        self.bucket = parse.path.strip("/")
        self.access = query_params.get("access", [None])[0]
        self.secret = query_params.get("secret", [None])[0]


class APIClient(Client):
    def __init__(self, url, config=None, environ=None):
        super(APIClient, self).__init__(url, config, environ)
        if self.logged is False:
            return
        adapter = requests.adapters.HTTPAdapter(
            pool_connections=3, pool_maxsize=300, max_retries=3
        )
        self.client = requests.Session()
        self.client.mount("http://", adapter)
        self.client.mount("https://", adapter)
        self.client.headers.update(
            {
                "Access-Key": self.access,
                "Secret-Key": self.secret,
                "Content-Type": "application/json",
            }
        )
        self.base_url = f"{self.scheme}://{self.netloc}/{self.bucket}"

    @lru_cache()
    def get_tags(self, name):
        url = f"{self.base_url}/nodes/{name}/tags"
        try:
            response = self.client.get(url)
            response.raise_for_status()
            result = response.json()
            value = result.get("tags")
            if value is None:
                return list()
            return list(value)
        except Exception:
            return list()

    @lru_cache()
    def get_node_properties(self, name, tags):
        url = f"{self.base_url}/nodes/{name}/{tags}"
        try:
            response = self.client.get(url)
            response.raise_for_status()
            result = response.json()
            return result.get("properties", {})
        except Exception:
            return {}

    @lru_cache()
    def get_args(self, name, tags, args):
        props = self.get_node_properties(name, tags)
        value = props.get(args)
        if value is None:
            return list()
        return value

    def exec_cql(self, cql):
        url = f"{self.base_url}/cypher/exec"
        try:
            response = self.client.post(url, json={"cql": cql})
            response.raise_for_status()
            result = response.json()
            value = result.get("args")
            if value is None:
                return str()
            return value
        except:
            return None


class S3Client(Client):
    def __init__(self, url, config=None, environ=None):
        super(S3Client, self).__init__(url, config, environ)
        if self.logged is False:
            return
        self.client = minio.Minio(
            self.netloc,
            access_key=self.access,
            secret_key=self.secret,
            secure=self.secure,
        )

    def upload(self, local_path, minio_path, **kwargs):
        progress = Loader(**kwargs, action="Upload")
        total = os.path.getsize(local_path)
        progress.set_meta(minio_path, total)
        if not self.client.bucket_exists(self.bucket):
            self.client.make_bucket(self.bucket)
        self.client.fput_object(self.bucket, minio_path, local_path, progress=progress)

    def download(self, minio_path, local_path, **kwargs):
        progress = Loader(**kwargs, action="Download")
        tmp_path = kwargs.get("tmp_path", str())
        stat = self.client.stat_object(self.bucket, minio_path)
        progress.set_meta(minio_path, stat.size)
        self.client.fget_object(
            self.bucket,
            minio_path,
            local_path,
            tmp_file_path=tmp_path,
            progress=progress,
        )

    def pack(self, archive_dir, output_pkg, **kwargs):
        packer = Packer(**kwargs)
        packer.pack(archive_dir, output_pkg)

    def unpack(self, archive_pkg, output_dir, **kwargs):
        packer = Packer(**kwargs)
        packer.unpack(archive_pkg, output_dir)

    def get_etag(self, minio_path):
        stat = self.client.stat_object(self.bucket, minio_path)
        return stat.etag


class DBPool(object):
    _instance = None
    _lock = threading.Lock()

    def __new__(cls, db_path, max_connections=10):
        with cls._lock:
            if cls._instance is None:
                cls._instance = super(DBPool, cls).__new__(cls)
                cls._instance.db_path = db_path
                cls._instance.max_connections = max_connections
                cls._instance._connections = []
                cls._instance._in_use = set()
                cls._instance._pool_lock = threading.Lock()
            return cls._instance

    def _create_connection(self):
        conn = sqlite3.connect(self.db_path, check_same_thread=False)
        return conn

    def get_connection(self):
        with self._pool_lock:
            for conn in self._connections:
                if conn not in self._in_use:
                    self._in_use.add(conn)
                    return conn

            if len(self._connections) < self.max_connections:
                conn = self._create_connection()
                self._connections.append(conn)
                self._in_use.add(conn)
                return conn

            while True:
                for conn in self._connections:
                    if conn not in self._in_use:
                        self._in_use.add(conn)
                        return conn
                time.sleep(0.1)

    def release_connection(self, conn):
        with self._pool_lock:
            if conn in self._in_use:
                self._in_use.remove(conn)

    def close_all(self):
        with self._pool_lock:
            for conn in self._connections:
                try:
                    conn.close()
                except Exception:
                    pass
            self._connections.clear()
            self._in_use.clear()


class DBContext(object):
    def __init__(self, pool):
        self.pool = pool
        self.conn = None
        self.cursor = None

    def __enter__(self):
        self.conn = self.pool.get_connection()
        self.cursor = self.conn.cursor()
        return self.conn, self.cursor

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.cursor:
            self.cursor.close()
        if self.conn:
            if exc_type:
                self.conn.rollback()
            self.pool.release_connection(self.conn)


class Syncer(object):
    def __new__(cls, config, environ, thispath):
        instance = super(Syncer, cls).__new__(cls)
        instance.config = config
        instance.environ = environ
        instance.thispath = thispath
        instance.storage_path = environ(instance.config.Env.STORAGE_PATH).getenv()
        instance.db_pool = DBPool(os.path.join(instance.storage_path, ".db"))
        os.makedirs(instance.storage_path, exist_ok=True)
        instance.locker = Locker()
        instance.__init_db()
        instance.s3_client = S3Client(
            instance.environ(instance.config.Env.STORAGE_URL).getenv(),
            instance.config,
            instance.environ,
        )

        instance.api_client = APIClient(
            instance.environ(instance.config.Env.RESTAPI_URL).getenv(),
            instance.config,
            instance.environ,
        )
        if all(
            (
                instance.s3_client.logged,
                instance.api_client.logged,
            )
        ):
            return instance
        return None

    def __del__(self):
        if hasattr(self, "db_pool"):
            self.db_pool.close_all()

    def __get_db(self):
        return DBContext(self.db_pool)

    def set_s3(self, url):
        return S3Client(url, self.config, self.environ)

    def set_api(self, url):
        return APIClient(url, self.config, self.environ)

    def get_tags(self, name):
        result = self.api_client.get_tags(name)
        return result

    def get_args(self, name, tags, args):
        result = self.api_client.get_args(name, tags, args)
        return result

    def sync_pkgs(self, path):
        this = self.thispath(path)
        if os.path.exists(this.root):
            if not self.clean_pkgs(path):
                return False
        name, tags, root = this.name, this.tags, this.root
        src_pkg = self.get_args(name, tags, "src")
        if not src_pkg:
            return False
        try:
            src_etag = self.s3_client.get_etag(src_pkg)
        except Exception:
            return False
        base_path = os.path.dirname(root)
        tar_pkg = root + ".pkg"
        cache_pkg = os.path.join(base_path, ".{}.{}.part.minio".format(tags, src_etag))
        if not os.path.exists(tar_pkg):
            with self.locker.start(base_path, tags, "download"):
                if not os.path.exists(tar_pkg):
                    self.s3_client.download(
                        src_pkg, tar_pkg, tmp_path=cache_pkg, name=name, tags=tags
                    )
        cache_dir = os.path.join(base_path, ".{}.{}.part.unpack".format(tags, src_etag))
        if not os.path.exists(root):
            with self.locker.start(base_path, tags, "unpacking"):
                if not os.path.exists(root):
                    self.s3_client.unpack(tar_pkg, cache_dir, name=name, tags=tags)
                    if os.name == "posix":
                        os.system("chmod -R +x {}".format(cache_dir))
                    self.write_db_etag(name, tags, src_etag)
                    os.rename(cache_dir, root)
                if os.path.exists(tar_pkg):
                    os.remove(tar_pkg)
        return True

    def clean_pkgs(self, path):
        this = self.thispath(path)
        base_path = os.path.dirname(this.root)
        if not base_path.startswith(self.storage_path):
            return False
        name, tags, root = this.name, this.tags, this.root
        src_pkg = self.get_args(name, tags, "src")
        if not src_pkg:
            return False
        if os.path.exists(root):
            src_etag = self.s3_client.get_etag(src_pkg)
            tar_etag = self.query_db_etag(name, tags)
            if src_etag == tar_etag:
                return False
        temp_tags = "." + tags + "." + uuid.uuid1().hex
        temp_root = os.path.join(base_path, temp_tags)
        try:
            os.rename(root, temp_root)
        except Exception:
            return False
        if self.config.VERBOSE == "+":
            sys.stdout.write("[{} {}] Update: {}\n".format(name, tags, root))
            sys.stdout.flush()
        for i in os.listdir(base_path):
            if i.startswith("." + tags + "."):
                try:
                    shutil.rmtree(os.path.join(base_path, i))
                except Exception:
                    pass
        return True

    def __init_db(self):
        try:
            with self.__get_db() as (db, cursor):
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS caches (
                        name TEXT,
                        tags TEXT,
                        etag TEXT NOT NULL,
                        timestamp INTEGER,
                        PRIMARY KEY (name, tags)
                    )
                """
                )
                db.commit()
                return True
        except sqlite3.Error as e:
            return False

    def write_db_etag(self, name, tags, etag):
        try:
            with self.__get_db() as (db, cursor):
                current_time = int(time.time())
                cursor.execute(
                    """
                    INSERT OR REPLACE INTO caches 
                    (name, tags, etag, timestamp)
                    VALUES (?, ?, ?, ?)
                """,
                    (name, tags, etag, current_time),
                )
                db.commit()
                return True
        except sqlite3.Error as e:
            return False

    def query_db_etag(self, name, tags):
        try:
            with self.__get_db() as (db, cursor):
                cursor.execute(
                    """
                    SELECT etag 
                    FROM caches 
                    WHERE name = ? AND tags = ?
                """,
                    (name, tags),
                )
                result = cursor.fetchone()
                return result[0] if result else None
        except sqlite3.Error as e:
            return False

    def update_timestamp(self, name, tags):
        try:
            with self.__get_db() as (db, cursor):
                current_time = int(time.time())
                cursor.execute(
                    """
                    UPDATE caches 
                    SET timestamp = ?
                    WHERE name = ? AND tags = ?
                """,
                    (current_time, name, tags),
                )
                db.commit()
                return cursor.rowcount > 0
        except sqlite3.Error as e:
            return False

    def clean_caches(self, days=30):
        deadline = int(time.time()) - days * 86400
        with self.__get_db() as (db, cursor):
            cursor.execute(
                """
                SELECT name, tags 
                FROM caches 
                WHERE timestamp < ?
            """,
                (deadline,),
            )
            rows = cursor.fetchall()
            if not rows:
                return True
            print("Wait Clean:", rows)
            for name, tags in rows:
                pkg_path = os.path.join(self.storage_path, name, tags)
                base_path = os.path.dirname(pkg_path)
                temp_tags = "." + tags + "." + uuid.uuid1().hex
                temp_path = os.path.join(base_path, temp_tags)
                if os.path.exists(pkg_path):
                    try:
                        os.rename(pkg_path, temp_path)
                        for i in os.listdir(base_path):
                            if i.startswith("." + tags + "."):
                                full_path = os.path.join(base_path, i)
                                shutil.rmtree(full_path)
                        if os.path.exists(base_path) and not os.listdir(base_path):
                            os.rmdir(base_path)
                    except Exception:
                        continue
                cursor.execute(
                    """
                    DELETE FROM caches 
                    WHERE name = ? AND tags = ?
                    """,
                    (name, tags),
                )
            db.commit()
            return True
