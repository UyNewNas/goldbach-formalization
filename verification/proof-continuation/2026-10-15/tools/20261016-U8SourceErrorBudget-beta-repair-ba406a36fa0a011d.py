from pathlib import Path
import hashlib,json
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
p=root/'ImbalancedChen/CurrentChenUpsilon8SourceErrorBudget.lean'
old=p.read_bytes();assert hashlib.sha256(old).hexdigest()=='f8a7e49a7e802d1dfc6459ee5ef0df4086f53e24b05464be05ffc59545aa7d29'
a=b'    rw [currentChenUpsilon8_eq_largeGoldbachPrimeTriples_add_errors]\n'
insert='''    change
      (((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
        ((currentChenUpsilon8UnitFibres N).card : ℝ)) / singularNormalization N =
        (currentChenUpsilon8 N -
          ((currentChenUpsilon8LargeGoldbachPrimeTriples N).card : ℝ)) / singularNormalization N
'''.encode()
assert old.count(a)==1
new=old.replace(a,insert+a)
assert new.replace(insert,b'')==old
p.write_bytes(new)
print(hashlib.sha256(new).hexdigest())
print('only actual goal beta reduction inserted; old/new bytes preserved by inverse')