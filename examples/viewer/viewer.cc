//
// Simple .obj viewer(vertex only)
//
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

#include <GL/glew.h>

#ifdef __APPLE__
#include <OpenGL/glu.h>
#else
#include <GL/glu.h>
#endif

#include <GLFW/glfw3.h>

#define TINYOBJLOADER_IMPLEMENTATION
#include "../../tiny_obj_loader.h"

#include "trackball.h"

#ifdef _WIN32
#ifdef __cplusplus
extern "C" {
#endif
#include <mmsystem.h>
#include <windows.h>
#ifdef __cplusplus
}
#endif
#pragma comment(lib, "winmm.lib")
#else
#if defined(__unix__) || defined(__APPLE__)
#include <sys/time.h>
#else
#include <ctime>
#endif
#endif

class timerutil {
 public:
#ifdef _WIN32
  typedef DWORD time_t;

  timerutil() { ::timeBeginPeriod(1); }
  ~timerutil() { ::timeEndPeriod(1); }

  void start() { t_[0] = ::timeGetTime(); }
  void end() { t_[1] = ::timeGetTime(); }

  time_t sec() { return (time_t)((t_[1] - t_[0]) / 1000); }
  time_t msec() { return (time_t)((t_[1] - t_[0])); }
  time_t usec() { return (time_t)((t_[1] - t_[0]) * 1000); }
  time_t current() { return ::timeGetTime(); }

#else
#if defined(__unix__) || defined(__APPLE__)
  typedef unsigned long int time_t;

  void start() { gettimeofday(tv + 0, &tz); }
  void end() { gettimeofday(tv + 1, &tz); }

  time_t sec() { return (time_t)(tv[1].tv_sec - tv[0].tv_sec); }
  time_t msec() {
    return this->sec() * 1000 +
           (time_t)((tv[1].tv_usec - tv[0].tv_usec) / 1000);
  }
  time_t usec() {
    return this->sec() * 1000000 + (time_t)(tv[1].tv_usec - tv[0].tv_usec);
  }
  time_t current() {
    struct timeval t;
    gettimeofday(&t, NULL);
    return (time_t)(t.tv_sec * 1000 + t.tv_usec);
  }

#else  // C timer
  // using namespace std;
  typedef clock_t time_t;

  void start() { t_[0] = clock(); }
  void end() { t_[1] = clock(); }

  time_t sec() { return (time_t)((t_[1] - t_[0]) / CLOCKS_PER_SEC); }
  time_t msec() { return (time_t)((t_[1] - t_[0]) * 1000 / CLOCKS_PER_SEC); }
  time_t usec() { return (time_t)((t_[1] - t_[0]) * 1000000 / CLOCKS_PER_SEC); }
  time_t current() { return (time_t)clock(); }

#endif
#endif

 private:
#ifdef _WIN32
  DWORD t_[2];
#else
#if defined(__unix__) || defined(__APPLE__)
  struct timeval tv[2];
  struct timezone tz;
#else
  time_t t_[2];
#endif
#endif
};

typedef struct {
  GLuint vb;  // vertex buffer
  int numTriangles;
} DrawObject;

std::vector<DrawObject> gDrawObjects;

int width = 768;
int height = 768;

double prevMouseX, prevMouseY;
bool mouseLeftPressed;
bool mouseMiddlePressed;
bool mouseRightPressed;
float curr_quat[4];
float prev_quat[4];
float eye[3], lookat[3], up[3];

GLFWwindow* window;

void CheckErrors(std::string desc) {
  GLenum e = glGetError();
  if (e != GL_NO_ERROR) {
    fprintf(stderr, "OpenGL error in \"%s\": %d (%d)\n", desc.c_str(), e, e);
    exit(20);
  }
}

void CalcNormal(float N[3], float v0[3], float v1[3], float v2[3]) {
  float v10[3];
  v10[0] = v1[0] - v0[0];
  v10[1] = v1[1] - v0[1];
  v10[2] = v1[2] - v0[2];

  float v20[3];
  v20[0] = v2[0] - v0[0];
  v20[1] = v2[1] - v0[1];
  v20[2] = v2[2] - v0[2];

  N[0] = v20[1] * v10[2] - v20[2] * v10[1];
  N[1] = v20[2] * v10[0] - v20[0] * v10[2];
  N[2] = v20[0] * v10[1] - v20[1] * v10[0];

  float len2 = N[0] * N[0] + N[1] * N[1] + N[2] * N[2];
  if (len2 > 0.0f) {
    float len = sqrtf(len2);

    N[0] /= len;
    N[1] /= len;
  }
}

bool LoadObjAndConvert(float bmin[3], float bmax[3],
                       std::vector<DrawObject>* drawObjects,
                       const char* filename) {
  tinyobj::attrib_t attrib;
  std::vector<tinyobj::shape_t> shapes;
  std::vector<tinyobj::material_t> materials;

  timerutil tm;

  tm.start();

  std::string err;
  bool ret =
      tinyobj::LoadObj(&attrib, &shapes, &materials, &err, filename, NULL);
  if (!err.empty()) {
    std::cerr << err << std::endl;
  }

  tm.end();

  if (!ret) {
    std::cerr << "Failed to load " << filename << std::endl;
    return false;
  }

  printf("Parsing time: %d [ms]\n", (int)tm.msec());

  printf("# of vertices  = %d\n", (int)(attrib.vertices.size()) / 3);
  printf("# of normals   = %d\n", (int)(attrib.normals.size()) / 3);
  printf("# of texcoords = %d\n", (int)(attrib.texcoords.size()) / 2);
  printf("# of materials = %d\n", (int)materials.size());
  printf("# of shapes    = %d\n", (int)shapes.size());

  bmin[0] = bmin[1] = bmin[2] = std::numeric_limits<float>::max();
  bmax[0] = bmax[1] = bmax[2] = -std::numeric_limits<float>::max();

  {
    for (size_t s = 0; s < shapes.size(); s++) {
      DrawObject o;
      std::vector<float> vb;  // pos(3float), normal(3float), color(3float)
      for (size_t f = 0; f < shapes[s].mesh.indices.size() / 3; f++) {
        tinyobj::index_t idx0 = shapes[s].mesh.indices[3 * f + 0];
        tinyobj::index_t idx1 = shapes[s].mesh.indices[3 * f + 1];
        tinyobj::index_t idx2 = shapes[s].mesh.indices[3 * f + 2];

        float v[3][3];
        for (int k = 0; k < 3; k++) {
          int f0 = idx0.vertex_index;
          int f1 = idx1.vertex_index;
          int f2 = idx2.vertex_index;
          assert(f0 >= 0);
          assert(f1 >= 0);
          assert(f2 >= 0);

          v[0][k] = attrib.vertices[3 * f0 + k];
          v[1][k] = attrib.vertices[3 * f1 + k];
          v[2][k] = attrib.vertices[3 * f2 + k];
          bmin[k] = std::min(v[0][k], bmin[k]);
          bmin[k] = std::min(v[1][k], bmin[k]);
          bmin[k] = std::min(v[2][k], bmin[k]);
          bmax[k] = std::max(v[0][k], bmax[k]);
          bmax[k] = std::max(v[1][k], bmax[k]);
          bmax[k] = std::max(v[2][k], bmax[k]);
        }

        float n[3][3];

        if (attrib.normals.size() > 0) {
          int f0 = idx0.normal_index;
          int f1 = idx1.normal_index;
          int f2 = idx2.normal_index;
          assert(f0 >= 0);
          assert(f1 >= 0);
          assert(f2 >= 0);
          for (int k = 0; k < 3; k++) {
            n[0][k] = attrib.normals[3 * f0 + k];
            n[1][k] = attrib.normals[3 * f1 + k];
            n[2][k] = attrib.normals[3 * f2 + k];
          }
        } else {
          // compute geometric normal
          CalcNormal(n[0], v[0], v[1], v[2]);
          n[1][0] = n[0][0];
          n[1][1] = n[0][1];
          n[1][2] = n[0][2];
          n[2][0] = n[0][0];
          n[2][1] = n[0][1];
          n[2][2] = n[0][2];
        }

        for (int k = 0; k < 3; k++) {
          vb.push_back(v[k][0]);
          vb.push_back(v[k][1]);
          vb.push_back(v[k][2]);
          vb.push_back(n[k][0]);
          vb.push_back(n[k][1]);
          vb.push_back(n[k][2]);
          // Use normal as color.
          float c[3] = {n[k][0], n[k][1], n[k][2]};
          float len2 = c[0] * c[0] + c[1] * c[1] + c[2] * c[2];
          if (len2 > 0.0f) {
            float len = sqrtf(len2);

            c[0] /= len;
            c[1] /= len;
            c[2] /= len;
          }
          vb.push_back(c[0] * 0.5 + 0.5);
          vb.push_back(c[1] * 0.5 + 0.5);
          vb.push_back(c[2] * 0.5 + 0.5);
        }
      }

      o.vb = 0;
      o.numTriangles = 0;
      if (vb.size() > 0) {
        glGenBuffers(1, &o.vb);
        glBindBuffer(GL_ARRAY_BUFFER, o.vb);
        glBufferData(GL_ARRAY_BUFFER, vb.size() * sizeof(float), &vb.at(0),
                     GL_STATIC_DRAW);
        o.numTriangles = vb.size() / 9 / 3;
        printf("shape[%d] # of triangles = %d\n", static_cast<int>(s),
               o.numTriangles);
      }

      drawObjects->push_back(o);
    }
  }

  printf("bmin = %f, %f, %f\n", bmin[0], bmin[1], bmin[2]);
  printf("bmax = %f, %f, %f\n", bmax[0], bmax[1], bmax[2]);

  return true;
}

void reshapeFunc(GLFWwindow* window, int w, int h) {
  int fb_w, fb_h;
  // Get actual framebuffer size.
  glfwGetFramebufferSize(window, &fb_w, &fb_h);

  glViewport(0, 0, fb_w, fb_h);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  gluPerspective(45.0, (float)w / (float)h, 0.01f, 100.0f);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity();

  width = w;
  height = h;
}

void keyboardFunc(GLFWwindow* window, int key, int scancode, int action,
                  int mods) {
  (void)window;
  (void)scancode;
  (void)mods;
  if (action == GLFW_PRESS || action == GLFW_REPEAT) {
    // Move camera
    float mv_x = 0, mv_y = 0, mv_z = 0;
    if (key == GLFW_KEY_K)
      mv_x += 1;
    else if (key == GLFW_KEY_J)
      mv_x += -1;
    else if (key == GLFW_KEY_L)
      mv_y += 1;
    else if (key == GLFW_KEY_H)
      mv_y += -1;
    else if (key == GLFW_KEY_P)
      mv_z += 1;
    else if (key == GLFW_KEY_N)
      mv_z += -1;
    // camera.move(mv_x * 0.05, mv_y * 0.05, mv_z * 0.05);
    // Close window
    if (key == GLFW_KEY_Q || key == GLFW_KEY_ESCAPE)
      glfwSetWindowShouldClose(window, GL_TRUE);

    // init_frame = true;
  }
}

void clickFunc(GLFWwindow* window, int button, int action, int mods) {
  (void)window;
  (void)mods;
  if (button == GLFW_MOUSE_BUTTON_LEFT) {
    if (action == GLFW_PRESS) {
      mouseLeftPressed = true;
      trackball(prev_quat, 0.0, 0.0, 0.0, 0.0);
    } else if (action == GLFW_RELEASE) {
      mouseLeftPressed = false;
    }
  }
  if (button == GLFW_MOUSE_BUTTON_RIGHT) {
    if (action == GLFW_PRESS) {
      mouseRightPressed = true;
    } else if (action == GLFW_RELEASE) {
      mouseRightPressed = false;
    }
  }
  if (button == GLFW_MOUSE_BUTTON_MIDDLE) {
    if (action == GLFW_PRESS) {
      mouseMiddlePressed = true;
    } else if (action == GLFW_RELEASE) {
      mouseMiddlePressed = false;
    }
  }
}

void motionFunc(GLFWwindow* window, double mouse_x, double mouse_y) {
  (void)window;
  float rotScale = 1.0f;
  float transScale = 2.0f;

  if (mouseLeftPressed) {
    trackball(prev_quat, rotScale * (2.0f * prevMouseX - width) / (float)width,
              rotScale * (height - 2.0f * prevMouseY) / (float)height,
              rotScale * (2.0f * mouse_x - width) / (float)width,
              rotScale * (height - 2.0f * mouse_y) / (float)height);

    add_quats(prev_quat, curr_quat, curr_quat);
  } else if (mouseMiddlePressed) {
    eye[0] -= transScale * (mouse_x - prevMouseX) / (float)width;
    lookat[0] -= transScale * (mouse_x - prevMouseX) / (float)width;
    eye[1] += transScale * (mouse_y - prevMouseY) / (float)height;
    lookat[1] += transScale * (mouse_y - prevMouseY) / (float)height;
  } else if (mouseRightPressed) {
    eye[2] += transScale * (mouse_y - prevMouseY) / (float)height;
    lookat[2] += transScale * (mouse_y - prevMouseY) / (float)height;
  }

  // Update mouse point
  prevMouseX = mouse_x;
  prevMouseY = mouse_y;
}

void Draw(const std::vector<DrawObject>& drawObjects) {
  glPolygonMode(GL_FRONT, GL_FILL);
  glPolygonMode(GL_BACK, GL_FILL);

  glEnable(GL_POLYGON_OFFSET_FILL);
  glPolygonOffset(1.0, 1.0);
  glColor3f(1.0f, 1.0f, 1.0f);
  for (size_t i = 0; i < drawObjects.size(); i++) {
    DrawObject o = drawObjects[i];
    if (o.vb < 1) {
      continue;
    }

    glBindBuffer(GL_ARRAY_BUFFER, o.vb);
    glEnableClientState(GL_VERTEX_ARRAY);
    glEnableClientState(GL_NORMAL_ARRAY);
    glEnableClientState(GL_COLOR_ARRAY);
    glVertexPointer(3, GL_FLOAT, 36, (const void*)0);
    glNormalPointer(GL_FLOAT, 36, (const void*)(sizeof(float) * 3));
    glColorPointer(3, GL_FLOAT, 36, (const void*)(sizeof(float) * 6));

    glDrawArrays(GL_TRIANGLES, 0, 3 * o.numTriangles);
    CheckErrors("drawarrays");
  }

  // draw wireframe
  glDisable(GL_POLYGON_OFFSET_FILL);
  glPolygonMode(GL_FRONT, GL_LINE);
  glPolygonMode(GL_BACK, GL_LINE);

  glColor3f(0.0f, 0.0f, 0.4f);
  for (size_t i = 0; i < drawObjects.size(); i++) {
    DrawObject o = drawObjects[i];
    if (o.vb < 1) {
      continue;
    }

    glBindBuffer(GL_ARRAY_BUFFER, o.vb);
    glEnableClientState(GL_VERTEX_ARRAY);
    glEnableClientState(GL_NORMAL_ARRAY);
    glDisableClientState(GL_COLOR_ARRAY);
    glVertexPointer(3, GL_FLOAT, 36, (const void*)0);
    glNormalPointer(GL_FLOAT, 36, (const void*)(sizeof(float) * 3));

    glDrawArrays(GL_TRIANGLES, 0, 3 * o.numTriangles);
    CheckErrors("drawarrays");
  }
}

static void Init() {
  trackball(curr_quat, 0, 0, 0, 0);

  eye[0] = 0.0f;
  eye[1] = 0.0f;
  eye[2] = 3.0f;

  lookat[0] = 0.0f;
  lookat[1] = 0.0f;
  lookat[2] = 0.0f;

  up[0] = 0.0f;
  up[1] = 1.0f;
  up[2] = 0.0f;
}

int main(int argc, char** argv) {
  if (argc < 2) {
    std::cout << "Needs input.obj\n" << std::endl;
    return 0;
  }

  Init();

  if (!glfwInit()) {
    std::cerr << "Failed to initialize GLFW." << std::endl;
    return -1;
  }

  window = glfwCreateWindow(width, height, "Obj viewer", NULL, NULL);
  if (window == NULL) {
    std::cerr << "Failed to open GLFW window. " << std::endl;
    glfwTerminate();
    return 1;
  }

  glfwMakeContextCurrent(window);
  glfwSwapInterval(1);

  // Callback
  glfwSetWindowSizeCallback(window, reshapeFunc);
  glfwSetKeyCallback(window, keyboardFunc);
  glfwSetMouseButtonCallback(window, clickFunc);
  glfwSetCursorPosCallback(window, motionFunc);

  glewExperimental = true;
  if (glewInit() != GLEW_OK) {
    std::cerr << "Failed to initialize GLEW." << std::endl;
    return -1;
  }

  reshapeFunc(window, width, height);

  float bmin[3], bmax[3];
  if (false == LoadObjAndConvert(bmin, bmax, &gDrawObjects, argv[1])) {
    return -1;
  }

  float maxExtent = 0.5f * (bmax[0] - bmin[0]);
  if (maxExtent < 0.5f * (bmax[1] - bmin[1])) {
    maxExtent = 0.5f * (bmax[1] - bmin[1]);
  }
  if (maxExtent < 0.5f * (bmax[2] - bmin[2])) {
    maxExtent = 0.5f * (bmax[2] - bmin[2]);
  }

  while (glfwWindowShouldClose(window) == GL_FALSE) {
    glfwPollEvents();
    glClearColor(0.1f, 0.2f, 0.3f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

    glEnable(GL_DEPTH_TEST);

    // camera & rotate
    glMatrixMode(GL_MODELVIEW);
    glLoadIdentity();
    GLfloat mat[4][4];
    gluLookAt(eye[0], eye[1], eye[2], lookat[0], lookat[1], lookat[2], up[0],
              up[1], up[2]);
    build_rotmatrix(mat, curr_quat);
    glMultMatrixf(&mat[0][0]);

    // Fit to -1, 1
    glScalef(1.0f / maxExtent, 1.0f / maxExtent, 1.0f / maxExtent);

    // Centerize object.
    glTranslatef(-0.5 * (bmax[0] + bmin[0]), -0.5 * (bmax[1] + bmin[1]),
                 -0.5 * (bmax[2] + bmin[2]));

    Draw(gDrawObjects);

    glfwSwapBuffers(window);
  }

  glfwTerminate();
}
