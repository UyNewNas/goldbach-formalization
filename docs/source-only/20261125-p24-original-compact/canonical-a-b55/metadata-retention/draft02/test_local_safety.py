"""Local solid-bundle fixtures only.  No canonical guard/main/remote task is run."""
import gzip
import hashlib
import io
import json
from pathlib import Path
import tempfile
import tarfile
import unittest
from unittest.mock import patch

import retention_common as c


class SolidRetentionSafety(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="p24-solid-fixture-", dir="/tmp")
        self.root = Path(self.temp.name); self.scripts = self.root/"scripts"; self.scripts.mkdir()
        self.work = self.root/"build"; self.work.mkdir()
        self.targets = []; self.archives = []
        for label in ["1087", "b55"]:
            folder = self.root/label; folder.mkdir()
            files = {}
            for i,name in enumerate(["registry-before.json","registry-after.json","full324-before-snapshot.json","full324-after-snapshot.json"]):
                raw = c.encoded({"fixture_label":label,"i":i})
                original = folder/name; original.write_bytes(raw); member = "promotion/"+name; files[member] = raw
                self.targets.append({"path":str(original),"bytes":len(raw),"sha256":c.sha(raw),"backup_id":label,
                                     "restore_kind":"inner_member","solid_member":"archives/evidence-"+label+".tar","member":member})
            index={n:{"bytes":len(b),"sha256":c.sha(b)} for n,b in files.items()}; files["FILES.json"]=c.encoded(index)
            buffer=io.BytesIO()
            with tarfile.open(fileobj=buffer,mode="w",format=tarfile.PAX_FORMAT) as tar:
                for name,raw in sorted(files.items()):
                    info=tarfile.TarInfo(name);info.size=len(raw);info.mtime=0;info.mode=0o644;tar.addfile(info,io.BytesIO(raw))
            tar_raw=buffer.getvalue();gz_raw=gzip.compress(tar_raw,mtime=0);gp=folder/(label+".tar.gz");gp.write_bytes(gz_raw)
            descriptor=folder/"descriptor.json";descriptor.write_bytes(c.encoded({"fixture":label}))
            self.archives.append({"id":label,"path":str(gp),"gzip_bytes":len(gz_raw),"gzip_sha256":c.sha(gz_raw),
                                  "git_blob_sha":hashlib.sha1(b"blob "+str(len(gz_raw)).encode()+b"\0"+gz_raw).hexdigest(),
                                  "tar_bytes":len(tar_raw),"tar_sha256":c.sha(tar_raw),
                                  "members":{n:{"bytes":len(b),"sha256":c.sha(b)} for n,b in files.items()},"file_count":len(files),
                                  "descriptor_path":str(descriptor),"descriptor_bytes":descriptor.stat().st_size,"descriptor_sha256":c.digest(descriptor)})
        for i in range(3):
            p=self.root/f"extra-{i}.json";p.write_bytes(c.encoded({"extra":i}))
            self.targets.append({"path":str(p),"bytes":p.stat().st_size,"sha256":c.digest(p),"backup_id":"supplement",
                                 "restore_kind":"outer_member","solid_member":f"extras/{i}.json","member":f"metadata/{i}.json"})
        for a in self.archives:
            self.targets.append({"path":a["path"],"bytes":a["gzip_bytes"],"sha256":a["gzip_sha256"],"backup_id":a["id"],
                                 "restore_kind":"gzip_from_tar","solid_member":"archives/evidence-"+a["id"]+".tar","member":None})
        self.manifest={"scripts_dir":str(self.scripts),"archives":self.archives,"targets":self.targets,"reserve_bytes":33554432}
        source=Path(__file__).resolve().parent
        for name in c.SCRIPT_NAMES: (self.scripts/name).write_bytes((source/name).read_bytes())
        (self.scripts/"retention-manifest.json").write_bytes(c.encoded(self.manifest))
        self.runtime=c.gzip_runtime_profile()
        self.expected={r["path"]:Path(r["path"]).read_bytes() for r in self.targets}

    def tearDown(self): self.temp.cleanup()

    def build(self):
        return c.build_solid_bundle(self.manifest,self.work,{"fixture_only":True},[c.check_target(r) for r in self.targets],self.runtime)[0]

    def test_all_thirteen_rebuild_without_any_original_loose_path(self):
        spec=self.build()
        moved=self.root/"held-original-fixtures";moved.mkdir()
        for i,r in enumerate(self.targets): Path(r["path"]).rename(moved/f"{i:02d}.bin")
        proof=self.root/"independent";proof.mkdir()
        rebuilt,verification=c.reconstruct_all(self.manifest,spec,proof,self.runtime)
        self.assertTrue(verification["all_thirteen_exact_bytes_reconstructed_from_solid_bundle_only"])
        self.assertEqual(len(rebuilt),13)
        for path,value in rebuilt.items(): self.assertEqual(value.read_bytes(),self.expected[path])

    def test_runtime_change_rejected_before_gzip_rebuild(self):
        spec=self.build();proof=self.root/"independent";proof.mkdir();wrong=dict(self.runtime,zlib_runtime_version="changed")
        with self.assertRaises(ValueError): c.reconstruct_all(self.manifest,spec,proof,wrong)
        self.assertTrue(all(Path(r["path"]).exists() for r in self.targets))

    def test_truncated_xz_rejected(self):
        spec=self.build();p=Path(spec["path"]);p.write_bytes(p.read_bytes()[:-1])
        with self.assertRaises(ValueError): c.verify_solid_bundle(spec)

    def test_incomplete_outer_inventory_rejected(self):
        spec=self.build()
        with self.assertRaises(ValueError): c.verify_solid_bundle(dict(spec,file_count=spec["file_count"]-1))

    def test_unknown_outer_extraction_rejected(self):
        spec=self.build();output=self.root/"must-not-exist"
        with self.assertRaises(ValueError): c.verify_solid_bundle(spec,extracts={"not-an-outer-member":output})
        self.assertFalse(output.exists())

    def test_insufficient_reconstruction_space_rejected_before_copy(self):
        spec=self.build();proof=self.root/"independent";proof.mkdir()
        with patch.object(c,"free_bytes",return_value=0):
            with self.assertRaises(ValueError): c.reconstruct_all(self.manifest,spec,proof,self.runtime)
        self.assertFalse((proof/"independent-inputs.tar.xz").exists())


if __name__ == "__main__": unittest.main(verbosity=2)
