"""Download only eight pinned, accepted GitHub Actions ZIPs. No Lean or Lake."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil

TRANSPORT_SHA256 = "6fdee2329166c014d14657df5098cd92aa5f1592305268bd4ef9be82e48915ee"
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit
from urllib.request import Request, HTTPRedirectHandler, build_opener

REPO = "UyNewNas/goldbach-formalization"
ROWS_SHA256 = "221a6758294a8284bc8e21036ed46bc79ceb6d5cc4917d28e50c98cf0b1d8742"
COHORTS = ("000-004","005-008","009-019","020-030","031-041","042-052","053-063","064-071")
BLOCK = 1024*1024
# Restore simultaneously needs these ZIPs and 73 source/object pairs.
# Warm cache happens after validated ZIP cleanup, not during acquisition.
STAGING_RESERVE = 3 * 1024**3

def need(test,message):
    if not test:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def load_rows(path):
    data = path.read_bytes()
    need(digest(data)==ROWS_SHA256, "Archive transport lock changed")
    rows = json.loads(data)
    need(tuple(row["cohort"] for row in rows)==COHORTS, "Archive cohort order changed")
    need(len({r["artifact"] for r in rows})==8 and len({r["run"] for r in rows})==8,
         "Archive artifact/run identities are not distinct")
    return rows

def bind_metadata(row, meta):
    run = meta.get("workflow_run") or {}
    need(meta.get("id")==row["artifact"] and run.get("id")==row["run"]
         and run.get("head_sha")==row["head"] and meta.get("name")==row["name"]
         and meta.get("expired") is False and meta.get("size_in_bytes")==row["bytes"]
         and meta.get("digest")=="sha256:"+row["sha256"]
         and ("expiry" not in row or meta.get("expires_at")==row["expiry"]),
         "Artifact metadata mismatch: "+row["cohort"])

def signed_request(url):
    try:
        q = urlsplit(url)
        valid = (q.scheme=="https" and q.username is None and q.password is None
                 and q.port in (None,443) and not q.fragment and bool(q.path)
                 and not any(ord(c) <= 32 or c == chr(127) for c in url)
                 and (q.hostname=="results-receiver.actions.githubusercontent.com"
                      or re.fullmatch(r"productionresultssa[0-9]+\.blob\.core\.windows\.net",q.hostname or "")))
    except (ValueError, TypeError):
        valid = False
    need(valid,"Unexpected GitHub release-asset storage destination")
    return Request(url,headers={"Accept-Encoding":"identity"})

def stream_checked(response, dst, row):
    need(response.status==200, "Artifact reply not a complete archive")
    enc = response.headers.get("Content-Encoding","identity")
    length = response.headers.get("Content-Length")
    need(enc=="identity" and length in (None,str(row["bytes"])), "Artifact byte envelope differs")
    if dst.exists() or dst.is_symlink():
        raise FileExistsError(dst)
    part = dst.with_suffix(".zip.partial")
    count = 0
    sha = hashlib.sha256()
    # Open before entering finally so a stale/unowned partial is never removed.
    out = part.open("xb")
    try:
        with out:
            remaining = row["bytes"]
            while remaining:
                chunk = response.read(min(remaining,BLOCK))
                if not chunk:
                    break
                need(len(chunk)<=remaining, "Artifact reply exceeds pinned size")
                remaining-=len(chunk)
                count+=len(chunk)
                out.write(chunk)
                sha.update(chunk)
            need(remaining==0 and not response.read(1) and sha.hexdigest()==row["sha256"],
                 "Artifact body length/digest mismatch: "+row["cohort"])
        # Atomic no-overwrite publication within one directory.
        os.link(part,dst)
    finally:
        part.unlink()
    return {"artifact":row["artifact"],"run":row["run"],"bytes":count,"sha256":sha.hexdigest()}

class StopRedirect(HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None

class Transport:
    def __init__(self, token):
        need(bool(token),"Missing GitHub job token")
        self.token = token
        self.opener = build_opener(StopRedirect())

    def open(self, request, timeout):
        return self.opener.open(request,timeout=timeout)

    def authenticated(self,row,zip_route=False):
        url = "https://api.github.com/repos/"+REPO+"/actions/artifacts/"+str(row["artifact"])
        if zip_route:
            url += "/zip"
        return Request(url,headers={"Authorization":"Bearer "+self.token,
                                    "Accept":"application/vnd.github+json",
                                    "X-GitHub-Api-Version":"2022-11-28"})

    def metadata(self,row):
        try:
            with self.open(self.authenticated(row),60) as r:
                need(r.status==200,"Wrong GitHub metadata response")
                payload = r.read(65537)
                need(len(payload)<=65536,"Oversized GitHub metadata")
                return json.loads(payload)
        except (URLError,OSError,json.JSONDecodeError):
            raise ValueError("GitHub artifact metadata request failed: "+row["cohort"]) from None

    def redirect(self,row):
        try:
            with self.open(self.authenticated(row,True),60):
                raise ValueError("Expected a single GitHub artifact redirect")
        except HTTPError as err:
            if err.code==302:
                return err.headers.get("Location","")
            raise ValueError("Artifact redirect request failed: "+row["cohort"]) from None
        except (URLError,OSError):
            raise ValueError("Artifact redirect request unavailable: "+row["cohort"]) from None

    def download(self,row,root):
        bind_metadata(row,self.metadata(row))
        req = signed_request(self.redirect(row))
        try:
            with self.open(req,120) as r:
                return stream_checked(r,root/(row["cohort"]+".zip"),row)
        except (URLError,OSError,ValueError) as err:
            # Underlying network exceptions can contain a signed query. Do not log them.
            raise ValueError("Verified ZIP transfer failed: "+row["cohort"]+
                             " ("+type(err).__name__+")") from None

def release_verified_zips(archives, rows, transport, transport_hash, logs):
    stamp_path = archives/"DOWNLOAD_RECEIPT.json"
    need(stamp_path.resolve(strict=True)==stamp_path, "Nonphysical download receipt")
    stamp = stamp_path.read_bytes()
    receipt=json.loads(stamp)
    expected={row["cohort"]:{k:row[k] for k in ("artifact","run","bytes","sha256")} for row in rows}
    need(receipt=={"status":"EIGHT_PINNED_ZIP_BYTES_VERIFIED",
                   "lock_sha256":ROWS_SHA256,"archives":expected,"lean_invoked":False},
         "Download receipt no longer matches locked artifacts")
    need(transport.resolve(strict=True)==transport,"Nonphysical restore receipt")
    restored=transport.read_bytes()
    need(digest(restored)==transport_hash,"Restored overlay provenance changed")
    payloads=[]
    for row in rows:
        p=archives/(row["cohort"]+".zip")
        need(p.resolve(strict=True)==p and p.is_file(),"Nonphysical validated ZIP")
        with p.open("rb") as f:
            need(p.stat().st_size==row["bytes"] and hashlib.file_digest(f,"sha256").hexdigest()==row["sha256"],
                 "ZIP bytes changed: "+row["cohort"])
        payloads.append(p)
    targets=((logs/"DOWNLOAD_RECEIPT.json",stamp),(logs/"TRANSPORT_RECEIPT.json",restored))
    need(not any(p.exists() or p.is_symlink() for p,_ in targets), "Would overwrite restore evidence")
    for p,data in targets:
        with p.open("xb") as f:
            f.write(data)
    # All eight and both receipts were checked before the first deletion.
    for p in payloads:
        p.unlink()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("mode",choices=("download","release"))
    p.add_argument("lock",type=Path)
    p.add_argument("archives",type=Path)
    p.add_argument("--overlay",type=Path)
    p.add_argument("--logs",type=Path)
    a=p.parse_args()
    need(os.environ.get("GITHUB_ACTIONS")=="true" and os.environ.get("GITHUB_REPOSITORY","").casefold()==REPO.casefold(),
         "Only the scoped GitHub Actions job can download")
    temp=Path(os.environ["RUNNER_TEMP"]).resolve(strict=True)
    archives=a.archives.absolute()
    need(archives.parent.resolve(strict=True)==archives.parent and archives.parent.is_relative_to(temp),
         "Archive destination outside physical runner scratch")
    rows=load_rows(a.lock)
    if a.mode == "release":
        need(a.overlay is not None and a.logs is not None, "Release requires overlay and log roots")
        roots=(archives,a.overlay.absolute(),a.logs.absolute())
        need(all(p.resolve(strict=True)==p and p.is_dir() and p.is_relative_to(temp) for p in roots)
             and all(not i.is_relative_to(j) for i in roots for j in roots if i!=j)
             and len(set(roots))==3,"Release paths must be physical disjoint runner scratch")
        release_verified_zips(archives,rows,roots[1]/"TRANSPORT_RECEIPT.json",TRANSPORT_SHA256,roots[2])
        return
    need(a.overlay is None and a.logs is None, "Unexpected download arguments")
    need(shutil.disk_usage(archives.parent).free >= STAGING_RESERVE+sum(r["bytes"] for r in rows),
         "Not enough staging space before dependency cache restore")
    archives.mkdir(mode=0o700)
    client=Transport(os.environ["GH_TOKEN"])
    completed={}
    for row in rows:
        completed[row["cohort"]]=client.download(row,archives)
        print("PINNED_ZIP_BYTES_VERIFIED",row["cohort"],row["bytes"],flush=True)
    with (archives/"DOWNLOAD_RECEIPT.json").open("x") as out:
        json.dump({"status":"EIGHT_PINNED_ZIP_BYTES_VERIFIED","lock_sha256":ROWS_SHA256,
                   "archives":completed,"lean_invoked":False},out,indent=2,sort_keys=True)
        out.write("\n")

if __name__=="__main__":
    main()
