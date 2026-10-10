#!/usr/bin/env python3
"""Local preview of the static edition.

    python3 tools/serve.py [--port 8765] [--prefix /nim-interactive/] [--dir dist]

Serves dist/ (or --dir) over HTTP.  With --prefix the site is served under that path only,
as it would be on a GitHub Pages project site (https://<user>.github.io/<repo>/); every
request outside the prefix returns 404, which exposes any root-relative link.
"""
import argparse
import functools
import http.server
import os
import posixpath
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class Handler(http.server.SimpleHTTPRequestHandler):
    prefix = "/"

    def translate_path(self, path):
        path = path.split("?", 1)[0].split("#", 1)[0]
        if not path.startswith(self.prefix):
            return os.path.join(self.directory, "__outside_prefix__")
        path = "/" + path[len(self.prefix):]
        return super().translate_path(path)

    def log_message(self, fmt, *args):
        if os.environ.get("SERVE_QUIET"):
            return
        super().log_message(fmt, *args)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--prefix", default="/")
    ap.add_argument("--dir", default=os.path.join(ROOT, "dist"))
    a = ap.parse_args()
    prefix = a.prefix if a.prefix.endswith("/") else a.prefix + "/"
    if not prefix.startswith("/"):
        prefix = "/" + prefix
    Handler.prefix = prefix
    handler = functools.partial(Handler, directory=os.path.abspath(a.dir))
    srv = http.server.ThreadingHTTPServer(("127.0.0.1", a.port), handler)
    print(f"Serving {a.dir} at http://127.0.0.1:{a.port}{prefix}  (Ctrl-C to stop)")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    sys.exit(main())
