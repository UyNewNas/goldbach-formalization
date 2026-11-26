"""Exact source-token quotations; Lean decoder equations are the only proof."""
import re

def nat(n):
 assert n.kind=='number' and re.fullmatch(r'0|[1-9][0-9]*',n.scalar)
 return n.scalar

def int_(n):
 assert n.kind in {'str','number'} and re.fullmatch(r'-?(0|[1-9][0-9]*)',n.scalar)
 return '('+n.scalar+' : Int)'

def rat(n):
 assert n.kind=='str'
 q=n.scalar.split('/')
 assert len(q) in [1,2] and all(re.fullmatch(r'-?(0|[1-9][0-9]*)',x) for x in q)
 return '('+' / '.join('('+x+' : ℚ)' for x in q)+')'

def arr(n,f):
 assert n.kind=='arr'
 return '#['+', '.join(f(x) for x in n.children)+']'

def record_value(key,n):
 if key=='vertices':return arr(n,rat)
 if key=='facet_vertices':return arr(n,nat)
 d={f.key.scalar:f.value for f in n.fields}
 if key=='vertex_values':
  return '{ gap := '+rat(d['gap'])+',\n    factors := '+arr(d['factors'],rat)+' }'
 if key=='face_ledger':
  return ('{ vertices := '+arr(d['vertices'],nat)+',\n'
          '    dimension := '+nat(d['dimension'])+', pivot := '+nat(d['pivot'])+',\n'
          '    facetSets := '+arr(d['facet_sets'],lambda x:arr(x,nat))+',\n'
          '    simplices := '+nat(d['simplices'])+' }')
 assert key=='simplices'
 return ('{ simplexId := '+nat(d['simplex_id'])+',\n'
         '    vertexIds := '+arr(d['vertex_ids'],nat)+',\n'
         '    physicalVolume := '+rat(d['physical_volume'])+',\n'
         '    meanGap := '+rat(d['mean_gap'])+',\n'
         '    factorMaxima := '+arr(d['factor_maxima'],rat)+',\n'
         '    gapWeightedMeans := '+arr(d['gap_weighted_means'],rat)+',\n'
         '    jensenBound := '+rat(d['jensen_bound'])+',\n'
         '    jensenFloorQ96 := '+int_(d['jensen_floor_Q96'])+' }')

