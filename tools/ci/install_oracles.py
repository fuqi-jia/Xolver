#!/usr/bin/env python3
"""Install the pinned independent cvc5 executable used by validation."""
import argparse
import hashlib
import http.client
from pathlib import Path
import platform
import sys
import time
import urllib.error
import urllib.request
import zipfile

VERSION = '1.4.2'
SHA256 = '7eb18f8c814c36a46c5a7d003983e9cfbc4b0a9828d6dd596239291bd4cc61d8'
# The immutable release asset is the same version/archive checked below. Use
# the official asset API rather than a failing browser-download redirect.
URL = 'https://api.github.com/repos/cvc5/cvc5/releases/assets/620335595'
DOWNLOAD_ATTEMPTS = 4


def download_archive(archive):
    temporary = archive.with_suffix('.download')
    try:
        for attempt in range(DOWNLOAD_ATTEMPTS):
            request = urllib.request.Request(URL, headers={
                'Accept': 'application/octet-stream',
                'X-GitHub-Api-Version': '2022-11-28',
            })
            try:
                with urllib.request.urlopen(request, timeout=60) as response, temporary.open('wb') as out:
                    while chunk := response.read(1024 * 1024):
                        out.write(chunk)
            except (urllib.error.URLError, TimeoutError, ConnectionError, http.client.IncompleteRead) as error:
                if isinstance(error, urllib.error.HTTPError) and error.code not in (408, 429, 500, 502, 503, 504):
                    raise
                if attempt + 1 == DOWNLOAD_ATTEMPTS:
                    raise
                status = f'HTTP {error.code}' if isinstance(error, urllib.error.HTTPError) else type(error).__name__
                print(f'Independent oracle download: {status}; retry {attempt + 1}/{DOWNLOAD_ATTEMPTS}', file=sys.stderr)
                time.sleep(2 ** attempt)
                continue
            if hashlib.sha256(temporary.read_bytes()).hexdigest() != SHA256:
                raise ValueError('independent solver archive checksum mismatch')
            temporary.replace(archive)
            return
    finally:
        temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    if platform.system() != 'Linux' or platform.machine() not in ('x86_64', 'amd64'):
        parser.error('this pinned distribution requires Linux x86_64')
    args.directory.mkdir(parents=True, exist_ok=True)
    archive = args.directory / f'cvc5-{VERSION}.zip'
    if not archive.exists() or hashlib.sha256(archive.read_bytes()).hexdigest() != SHA256:
        download_archive(archive)
    with zipfile.ZipFile(archive) as source:
        executable = next(n for n in source.namelist() if n.endswith('/bin/cvc5'))
        target = args.directory / 'cvc5'
        target.write_bytes(source.read(executable))
        target.chmod(0o755)
        for name in source.namelist():
            if not name.endswith('/') and ('/licenses/' in name or Path(name).name in ('COPYING', 'AUTHORS')):
                destination = args.directory / 'licenses' / Path(name).name
                destination.parent.mkdir(exist_ok=True)
                destination.write_bytes(source.read(name))
    print(f'cvc5 {VERSION}: {target}; archive SHA-256 {SHA256}')


if __name__ == '__main__':
    main()
