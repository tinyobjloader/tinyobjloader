// osd_refine — OpenSubdiv (Far, CPU) reference for the subdivision tags.
//
//   osd_refine FILE.obj LEVEL [--limit]
//
// Loads FILE.obj with the tinyobjloader C++ loader (triangulate = false),
// checks each shape's `t` lines with tobj_subd (subd-obj.md), builds a
// Far::TopologyRefiner with the scheme, boundary rules, creases, corners and
// holes, refines uniformly to LEVEL and prints, per shape,
//
//   shape <name> <number of points>
//   x y z            (one line per refined vertex; with --limit, the vertex
//                     projected to the limit surface)
//
// A shape uses only the vertices its faces refer to, in increasing file order
// (as the Blender add-on imports it). Tags that are absent take
// OpenSubdiv's Sdc::Options defaults. Shapes whose tags are rejected are
// reported on stderr and skipped.
//
// Build (CPU-only OpenSubdiv):
//   cc  -std=c11 -c tobj_subd.c -o tobj_subd.o
//   c++ -std=c++17 -I<osd>/include blender/tests/osd_refine.cc tobj_subd.o \
//       -L<osd>/lib -losdCPU -o osd_refine
#define TINYOBJLOADER_IMPLEMENTATION
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <vector>

#include <opensubdiv/far/primvarRefiner.h>
#include <opensubdiv/far/topologyDescriptor.h>

#include "../../tiny_obj_loader.h"
#include "../../tobj_subd.h"

using namespace OpenSubdiv;

struct Point {
  float p[3];
  void Clear(void * = nullptr) { p[0] = p[1] = p[2] = 0.0f; }
  void AddWithWeight(Point const &s, float w) {
    p[0] += w * s.p[0];
    p[1] += w * s.p[1];
    p[2] += w * s.p[2];
  }
};

int main(int argc, char **argv) {
  if (argc < 3) {
    std::fprintf(stderr, "usage: osd_refine FILE.obj LEVEL [--limit]\n");
    return 2;
  }
  const int level = std::atoi(argv[2]);
  const bool limit = argc > 3 && std::string(argv[3]) == "--limit";
  tinyobj::ObjReaderConfig cfg;
  cfg.triangulate = false;
  tinyobj::ObjReader reader;
  if (!reader.ParseFromFile(argv[1], cfg)) {
    std::fprintf(stderr, "load failed: %s\n", reader.Error().c_str());
    return 1;
  }
  const std::vector<tinyobj::real_t> &pos = reader.GetAttrib().vertices;

  for (const tinyobj::shape_t &sh : reader.GetShapes()) {
    const tinyobj::mesh_t &m = sh.mesh;
    std::vector<int> vi;
    for (const tinyobj::index_t &i : m.indices) vi.push_back(i.vertex_index);
    std::vector<const char *> lines;
    for (const std::string &l : m.tag_lines) lines.push_back(l.c_str());
    tobj_subd s;
    if (tobj_subd_parse_lines(lines.data(), lines.size(), m.num_face_vertices.data(),
                              m.num_face_vertices.size(), vi.data(), &s))
      return 1;
    if (!s.ok) {
      std::fprintf(stderr, "shape %s: tags rejected (%s)\n", sh.name.c_str(),
                   s.num_errors ? s.errors[0] : "?");
      tobj_subd_free(&s);
      continue;
    }

    // compact to the shape's own vertices, in increasing file order
    std::map<int, int> local;
    for (int v : vi) local[v] = 0;
    int n = 0;
    for (auto &kv : local) kv.second = n++;
    std::vector<Far::Index> fv;
    for (int v : vi) fv.push_back(local[v]);
    std::vector<int> nverts(m.num_face_vertices.begin(), m.num_face_vertices.end());

    std::vector<Far::Index> creasePairs, corners, holes;
    std::vector<float> creaseW, cornerW;
    for (size_t i = 0; i < s.num_creases; i++) {
      creasePairs.push_back(local[(int)s.creases[i].v0]);
      creasePairs.push_back(local[(int)s.creases[i].v1]);
      creaseW.push_back((float)tobj_subd_sharpness(s.creases[i].sharpness));
    }
    for (size_t i = 0; i < s.num_corners; i++) {
      corners.push_back(local[(int)s.corners[i].v]);
      cornerW.push_back((float)tobj_subd_sharpness(s.corners[i].sharpness));
    }
    for (size_t i = 0; i < s.num_holes; i++) holes.push_back((Far::Index)s.holes[i]);

    Sdc::SchemeType scheme = s.scheme == TOBJ_SUBD_LOOP       ? Sdc::SCHEME_LOOP
                             : s.scheme == TOBJ_SUBD_BILINEAR ? Sdc::SCHEME_BILINEAR
                                                              : Sdc::SCHEME_CATMARK;
    Sdc::Options opt;
    // Absent tags: OpenSubdiv's OBJ reader defaults (subd-obj.md): edge-only
    // boundary; the other Sdc defaults already match.
    opt.SetVtxBoundaryInterpolation(Sdc::Options::VTX_BOUNDARY_EDGE_ONLY);
    // Tag values follow OpenSubdiv's OBJ reader (regression/common/far_utils.h),
    // which is not the Sdc enum order: 1 = edge and corner, 2 = edge only.
    if (s.interp_boundary == 0)
      opt.SetVtxBoundaryInterpolation(Sdc::Options::VTX_BOUNDARY_NONE);
    else if (s.interp_boundary == 1)
      opt.SetVtxBoundaryInterpolation(Sdc::Options::VTX_BOUNDARY_EDGE_AND_CORNER);
    else if (s.interp_boundary == 2)
      opt.SetVtxBoundaryInterpolation(Sdc::Options::VTX_BOUNDARY_EDGE_ONLY);
    if (s.fvar_interp_boundary != TOBJ_SUBD_UNSET)
      opt.SetFVarLinearInterpolation(
          (Sdc::Options::FVarLinearInterpolation)s.fvar_interp_boundary);
    if (s.crease_method != TOBJ_SUBD_UNSET)
      opt.SetCreasingMethod((Sdc::Options::CreasingMethod)s.crease_method);
    if (s.smooth_triangles != TOBJ_SUBD_UNSET)
      opt.SetTriangleSubdivision((Sdc::Options::TriangleSubdivision)s.smooth_triangles);

    Far::TopologyDescriptor desc;
    desc.numVertices = n;
    desc.numFaces = (int)nverts.size();
    desc.numVertsPerFace = nverts.data();
    desc.vertIndicesPerFace = fv.data();
    desc.numCreases = (int)creaseW.size();
    desc.creaseVertexIndexPairs = creasePairs.data();
    desc.creaseWeights = creaseW.data();
    desc.numCorners = (int)cornerW.size();
    desc.cornerVertexIndices = corners.data();
    desc.cornerWeights = cornerW.data();
    desc.numHoles = (int)holes.size();
    desc.holeIndices = holes.data();

    typedef Far::TopologyRefinerFactory<Far::TopologyDescriptor> Factory;
    Far::TopologyRefiner *refiner =
        Factory::Create(desc, Factory::Options(scheme, opt));
    if (!refiner) {
      std::fprintf(stderr, "shape %s: OpenSubdiv rejected the topology\n", sh.name.c_str());
      tobj_subd_free(&s);
      continue;
    }
    // Limit positions: PrimvarRefiner::Limit applies limit masks, which are
    // exact only where no semi-sharp feature remains. Refine further until
    // every finite sharpness has decayed (one unit per level), take the limit
    // there and follow each level-LEVEL vertex down its child-vertex chain.
    int deep = level;
    if (limit) {
      float smax = 0.0f;
      for (float w : creaseW) if (w < 10.0f && w > smax) smax = w;
      for (float w : cornerW) if (w < 10.0f && w > smax) smax = w;
      int need = (int)std::ceil(smax);
      if (need > deep) deep = need;
    }
    Far::TopologyRefiner::UniformOptions uopt(deep);
    uopt.fullTopologyInLastLevel = limit;  // required by PrimvarRefiner::Limit
    refiner->RefineUniform(uopt);

    std::vector<Point> buf(refiner->GetNumVerticesTotal());
    Point *src = buf.data();
    for (auto &kv : local)
      for (int k = 0; k < 3; k++) src[kv.second].p[k] = (float)pos[3 * kv.first + k];
    Far::PrimvarRefiner primvar(*refiner);
    Point *at_level = src;
    for (int l = 1; l <= deep; l++) {
      Point *dst = src + refiner->GetLevel(l - 1).GetNumVertices();
      primvar.Interpolate(l, src, dst);
      src = dst;
      if (l == level) at_level = src;
    }
    const int nlast = refiner->GetLevel(level).GetNumVertices();
    std::vector<Point> out(at_level, at_level + nlast);
    if (limit) {
      const int ndeep = refiner->GetLevel(deep).GetNumVertices();
      std::vector<Point> lim(ndeep);
      primvar.Limit(std::vector<Point>(src, src + ndeep), lim);
      for (int v = 0; v < nlast; v++) {
        Far::Index c = v;
        for (int l = level; l < deep; l++) c = refiner->GetLevel(l).GetVertexChildVertex(c);
        out[v] = lim[c];
      }
    }

    std::printf("shape %s %d\n", sh.name.c_str(), nlast);
    for (const Point &p : out) std::printf("%.7g %.7g %.7g\n", p.p[0], p.p[1], p.p[2]);
    delete refiner;
    tobj_subd_free(&s);
  }
  return 0;
}
