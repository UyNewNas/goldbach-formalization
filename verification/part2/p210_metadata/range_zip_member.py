#!/usr/bin/env python3
"""Read one existing Actions ZIP member with HTTP Range; never run Lean.

Supply ZIP_RANGE_URL for an already issued download URL, or --repo/--artifact
with GH_TOKEN on an authorized runner. The GitHub token is sent only to the
GitHub API redirect request, never to the redirected storage host.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import urllib.error
import urllib.request
import zipfile


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def github_url(repo, artifact):
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repo):
        raise ValueError('Invalid repository name')
    token = os.environ['GH_TOKEN']
    request = urllib.request.Request(
        f'https://api.github.com/repos/{repo}/actions/artifacts/{artifact}/zip',
        headers={'Authorization': 'Bearer '+token,
                 'Accept': 'application/vnd.github+json',
                 'X-GitHub-Api-Version': '2022-11-28'})
    try:
        with urllib.request.build_opener(NoRedirect()).open(request) as response:
            raise RuntimeError('Expected a GitHub artifact redirect; refused a full response')
    except urllib.error.HTTPError as response:
        if response.code not in (301, 302, 303, 307, 308):
            raise
        location = response.headers['Location']
        if not location.startswith('https://'):
            raise RuntimeError('Non-HTTPS storage redirect')
        return location


class RangeFile(io.RawIOBase):
    def __init__(self, url, size):
        self.url, self.size, self.pos = url, size, 0
        self.transferred, self.ranges = 0, []

    def seekable(self): return True
    def readable(self): return True
    def tell(self): return self.pos

    def seek(self, offset, whence=0):
        self.pos = offset if whence == 0 else self.pos+offset if whence == 1 else self.size+offset
        if self.pos < 0: raise ValueError('Negative ZIP seek')
        return self.pos

    def read(self, count=-1):
        if count < 0: count = self.size-self.pos
        count = min(count, self.size-self.pos)
        if count <= 0: return b''
        start, end = self.pos, self.pos+count-1
        request = urllib.request.Request(self.url, headers={'Range': f'bytes={start}-{end}'})
        with urllib.request.urlopen(request) as response:
            if response.status != 206:
                raise RuntimeError('Storage did not honor Range; refused a full download')
            if response.headers.get('Content-Range') != f'bytes {start}-{end}/{self.size}':
                raise RuntimeError('Unexpected Content-Range/ZIP size')
            data = response.read(count+1)
        if len(data) != count: raise RuntimeError('Incomplete or excessive Range response')
        self.pos += count
        self.transferred += count
        self.ranges.append([start,end])
        return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo')
    parser.add_argument('--artifact', type=int)
    parser.add_argument('--archive-size', type=int, required=True)
    parser.add_argument('--member', required=True)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--metadata', type=Path, required=True)
    args = parser.parse_args()
    if not re.fullmatch(r'[0-9a-f]{64}', args.sha256): raise ValueError('Expected SHA256')
    if args.out.exists():
        if hashlib.sha256(args.out.read_bytes()).hexdigest() != args.sha256:
            raise RuntimeError('Existing member has different bytes; refusing overwrite')
        print('Reused existing SHA-verified member:', args.out)
        return
    url = os.environ.get('ZIP_RANGE_URL')
    if not url:
        if not args.repo or not args.artifact: raise ValueError('Supply ZIP_RANGE_URL or --repo/--artifact')
        url = github_url(args.repo, args.artifact)
    stream = RangeFile(url, args.archive_size)
    with zipfile.ZipFile(stream) as archive:
        info = archive.getinfo(args.member)
        raw = archive.read(args.member)  # zipfile also verifies the member CRC32.
    actual = hashlib.sha256(raw).hexdigest()
    if actual != args.sha256: raise RuntimeError('Member differs from its existing compile record')
    metadata = {'repository': args.repo, 'artifact_id': args.artifact,
        'archive_bytes': args.archive_size, 'member': args.member,
        'member_bytes': len(raw), 'member_compressed_bytes': info.compress_size,
        'member_crc32': hex(info.CRC), 'member_sha256': actual,
        'range_bytes_read': stream.transferred, 'ranges': stream.ranges,
        'full_zip_hash_recomputed_locally': False, 'source_compilations': 0}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_bytes(raw)
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.write_text(json.dumps(metadata, sort_keys=True, indent=2)+'\n')
    print(json.dumps(metadata, sort_keys=True))


if __name__ == '__main__': main()
