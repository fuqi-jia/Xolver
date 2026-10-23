#!/usr/bin/env python3
"""Install the pinned independent cvc5 executable used by validation."""
import argparse
import hashlib
from pathlib import Path
import platform
import urllib.request
import zipfile

VERSION = '1.4.2'
SHA256 = '7eb18f8c814c36a46c5a7d003983e9cfbc4b0a9828d6dd596239291bd4cc61d8'
URL = f'https://github.com/cvc5/cvc5/releases/download/cvc5-{VERSION}/cvc5-Linux-x86_64-static.zip'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    if platform.system() != 'Linux' or platform.machine() not in ('x86_64', 'amd64'):
        parser.error('this pinned distribution requires Linux x86_64')
    args.directory.mkdir(parents=True, exist_ok=True)
    archive = args.directory / f'cvc5-{VERSION}.zip'
    if not archive.exists() or hashlib.sha256(archive.read_bytes()).hexdigest() != SHA256:
        temporary = archive.with_suffix('.download')
        with urllib.request.urlopen(URL, timeout=60) as response, temporary.open('wb') as out:
            while chunk := response.read(1024 * 1024):
                out.write(chunk)
        if hashlib.sha256(temporary.read_bytes()).hexdigest() != SHA256:
            raise ValueError('independent solver archive checksum mismatch')
        temporary.replace(archive)
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
