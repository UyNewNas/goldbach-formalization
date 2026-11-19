// Exact-data numerical replay of P1OriginalFourthGuillotine.check 64.
// This is not a Lean proof, not native_decide, and does not invoke the kernel.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

struct Row { std::array<std::uint16_t,4> lo,hi; std::uint8_t mask; };
struct Stats {
  std::uint64_t nodes=0, empty=0, singleton=0, cuts=0, unary=0, binary=0;
  std::array<std::uint64_t,4> axis{}; unsigned max_depth=0;
  std::uint64_t failed_n=0; unsigned failed_depth=0; std::string reason;
};
using Point=std::array<unsigned,4>;

bool check(std::vector<Row>& rs,std::size_t l,std::size_t r,
           Point a,Point b,unsigned fuel,unsigned depth,Stats& st) {
  ++st.nodes; st.max_depth=std::max(st.max_depth,depth);
  const std::size_t n=r-l;
  if(n==0){++st.empty;return true;}
  if(n==1){++st.singleton;return true;}
  if(fuel==0){st.reason="fuel exhausted";st.failed_n=n;st.failed_depth=depth;return false;}
  unsigned cut=4,mid=0;
  for(unsigned i=0;i<4;++i){
    if(b[i]-a[i]<=1) continue;
    unsigned m=(a[i]+b[i])/2; bool good=true;
    for(std::size_t j=l;j<r;++j){
      if(!(rs[j].hi[i]<=m || m<=rs[j].lo[i])){good=false;break;}
    }
    if(good){cut=i;mid=m;break;}
  }
  if(cut==4){st.reason="no valid midpoint";st.failed_n=n;st.failed_depth=depth;return false;}
  ++st.cuts;++st.axis[cut];
  auto pivot=std::partition(rs.begin()+l,rs.begin()+r,[cut,mid](const Row& x){return x.hi[cut]<=mid;});
  std::size_t m=static_cast<std::size_t>(pivot-rs.begin());
  if(m==l || m==r) ++st.unary; else ++st.binary;
  Point bl=b;bl[cut]=mid;Point ar=a;ar[cut]=mid;
  return check(rs,l,m,a,bl,fuel-1,depth+1,st) &&
         check(rs,m,r,ar,b,fuel-1,depth+1,st);
}
Row box(unsigned l,unsigned h){Row r{};for(unsigned i=0;i<4;++i){r.lo[i]=l;r.hi[i]=h;}return r;}
bool run(std::vector<Row> rows,unsigned fuel,Stats& st){return check(rows,0,rows.size(),Point{0,0,0,0},Point{65536,65536,65536,65536},fuel,0,st);}
bool self_test(){
  Stats a,b,c,d,e,f;
  Row x=box(128,256),y=box(256,384),z=box(192,320);
  // Disjoint boxes need not satisfy this particular dyadic-midpoint checker.
  Row nondyadic1=box(100,200),nondyadic2=box(200,300);
  return run({},64,a) && run({x},0,b) && run({x,y},64,c) &&
         !run({x,z},64,d) && !run({x,y},0,e) &&
         !run({nondyadic1,nondyadic2},64,f);
}
int main(int argc,char** argv){
  bool micro=argc==3 && std::string(argv[1])=="--micro";
  if(argc!=2 && !micro){std::cerr<<"usage: guillotine_check [--micro] WIRE17\n";return 2;}
  if(!self_test()){std::cerr<<"self-test failed\n";return 3;}
  constexpr std::size_t bytes_per=17;
  std::ifstream input(argv[micro?2:1],std::ios::binary | std::ios::ate);
  if(!input){std::cerr<<"cannot open input\n";return 4;}
  auto size=input.tellg();
  if(size<0 || size%bytes_per!=0){std::cerr<<"invalid input size\n";return 5;}
  std::size_t count=static_cast<std::size_t>(size)/bytes_per;
  if((!micro && count!=3699127) || (micro && count>100)){std::cerr<<"unexpected row count\n";return 5;}
  input.seekg(0);
  std::vector<Row> rows;rows.reserve(count);
  std::array<unsigned char,bytes_per> buf{};
  for(std::size_t j=0;j<count;++j){
    if(!input.read(reinterpret_cast<char*>(buf.data()),buf.size())){std::cerr<<"short input\n";return 5;}
    Row row{};for(unsigned i=0;i<4;++i){row.lo[i]=std::uint16_t(buf[2*i])+256u*buf[2*i+1];row.hi[i]=std::uint16_t(buf[8+2*i])+256u*buf[9+2*i];}row.mask=buf[16];rows.push_back(row);
  }
  if(input.peek()!=std::char_traits<char>::eof()){std::cerr<<"trailing input\n";return 6;}
  Stats st;bool ok=check(rows,0,rows.size(),Point{0,0,0,0},Point{65536,65536,65536,65536},64,0,st);
  std::cout<<"{\"pass\":"<<(ok?"true":"false")<<",\"rows\":"<<rows.size()
           <<",\"nodes\":"<<st.nodes<<",\"empty_leaves\":"<<st.empty<<",\"singletons\":"<<st.singleton
           <<",\"cuts\":"<<st.cuts<<",\"unary_cuts\":"<<st.unary<<",\"binary_cuts\":"<<st.binary
           <<",\"axis_cuts\":["<<st.axis[0]<<","<<st.axis[1]<<","<<st.axis[2]<<","<<st.axis[3]<<"]"
           <<",\"max_depth\":"<<st.max_depth<<",\"reason\":\""<<st.reason<<"\",\"failed_rows\":"<<st.failed_n<<",\"failed_depth\":"<<st.failed_depth<<"}\n";
  if(ok && (st.singleton!=count || st.nodes!=2*st.cuts+1 || st.cuts!=st.unary+st.binary)){std::cerr<<"internal statistics mismatch\n";return 7;}
  return ok?0:1;
}
