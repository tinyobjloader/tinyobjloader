#include <math.h>
#include <GL/glew.h>

#ifdef __APPLE__
#include <OpenGL/glu.h>
#else
#include <GL/glu.h>
#endif

#include <GLFW/glfw3.h>

#include "trackball.h"

#define TINYOBJ_LOADER_C_IMPLEMENTATION
#include "tinyobj_loader_c.h"

#define MAX_OBJECTS (128)

typedef struct {
  GLuint vb;
  int numTriangles;
} DrawObject;

static DrawObject gDrawObjects[MAX_OBJECTS];
static int gNumDrawObjects;

static int width = 768;
static int height = 768;

static float prevMouseX, prevMouseY;
static int mouseLeftPressed;
static int mouseMiddlePressed;
static int mouseRightPressed;
static float curr_quat[4];
static float prev_quat[4];
static float eye[3], lookat[3], up[3];

static GLFWwindow* gWindow;

static void CheckErrors(const char* desc) {
  GLenum e = glGetError();
  if (e != GL_NO_ERROR) {
    fprintf(stderr, "OpenGL error in \"%s\": %d (%d)\n", desc, e, e);
    exit(20);
  }
}

static void CalcNormal(float N[3], float v0[3], float v1[3], float v2[3]) {
  float v10[3];
  float v20[3];
  float len2;

  v10[0] = v1[0] - v0[0];
  v10[1] = v1[1] - v0[1];
  v10[2] = v1[2] - v0[2];

  v20[0] = v2[0] - v0[0];
  v20[1] = v2[1] - v0[1];
  v20[2] = v2[2] - v0[2];

  N[0] = v20[1] * v10[2] - v20[2] * v10[1];
  N[1] = v20[2] * v10[0] - v20[0] * v10[2];
  N[2] = v20[0] * v10[1] - v20[1] * v10[0];

  len2 = N[0] * N[0] + N[1] * N[1] + N[2] * N[2];
  if (len2 > 0.0f) {
    float len = sqrt(len2);
    
    N[0] /= len;
    N[1] /= len;
  }
}

static const char *mmap_file(size_t *len, const char* filename)
{
#ifdef _WIN64
  HANDLE file = CreateFileA(filename, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL | FILE_FLAG_SEQUENTIAL_SCAN, NULL);
    assert(file != INVALID_HANDLE_VALUE);

    HANDLE fileMapping = CreateFileMapping(file, NULL, PAGE_READONLY, 0, 0, NULL);
    assert(fileMapping != INVALID_HANDLE_VALUE);
 
    LPVOID fileMapView = MapViewOfFile(fileMapping, FILE_MAP_READ, 0, 0, 0);
    auto fileMapViewChar = (const char*)fileMapView;
    assert(fileMapView != NULL);
#else

  FILE* f;
  long file_size;
  struct stat sb;
  char *p;
  int fd;

  (*len) = 0;

  f = fopen(filename, "r" );
  fseek(f, 0, SEEK_END);
  file_size = ftell(f);
  fclose(f);

  fd = open (filename, O_RDONLY);
  if (fd == -1) {
    perror ("open");
    return NULL;
  }

  if (fstat (fd, &sb) == -1) {
    perror ("fstat");
    return NULL;
  }

  if (!S_ISREG (sb.st_mode)) {
    fprintf (stderr, "%s is not a file\n", "lineitem.tbl");
    return NULL;
  }

  p = (char*)mmap (0, (size_t)file_size, PROT_READ, MAP_SHARED, fd, 0);

  if (p == MAP_FAILED) {
    perror ("mmap");
    return NULL;
  }

  if (close (fd) == -1) {
    perror ("close");
    return NULL;
  }

  (*len) = (size_t)file_size;

  return p;
  
#endif
}

#if 0
static int gz_load(std::vector<char>* buf, const char* filename)
{
#ifdef ENABLE_ZLIB
    gzFile file;
    file = gzopen (filename, "r");
    if (! file) {
        fprintf (stderr, "gzopen of '%s' failed: %s.\n", filename,
                 strerror (errno));
        exit (EXIT_FAILURE);
        return false;
    }
    while (1) {
        int err;                    
        int bytes_read;
        unsigned char buffer[1024];
        bytes_read = gzread (file, buffer, 1024);
        buf->insert(buf->end(), buffer, buffer + 1024); 
        //printf ("%s", buffer);
        if (bytes_read < 1024) {
            if (gzeof (file)) {
                break;
            }
            else {
                const char * error_string;
                error_string = gzerror (file, & err);
                if (err) {
                    fprintf (stderr, "Error: %s.\n", error_string);
                    exit (EXIT_FAILURE);
                    return false;
                }
            }
        }
    }
    gzclose (file);
    return true;
#else
  return false;
#endif
}
#endif

static const char* get_file_data(size_t *len, const char* filename)
{

  const char *ext = strrchr(filename, '.');

  size_t data_len = 0;
  const char* data = NULL;

  if (strcmp(ext, ".gz") == 0) {
    assert(0); /* todo */

#if 0
    std::vector<char> buf;
    bool ret = gz_load(&buf, filename);

    if (ret) {
      char *p = static_cast<char*>(malloc(buf.size() + 1));  // @fixme { implement deleter }
      memcpy(p, &buf.at(0), buf.size());
      p[buf.size()] = '\0';
      data = p;
      data_len = buf.size();
    }
#endif

  } else {
    
    data = mmap_file(&data_len, filename);
  }

  (*len) = data_len;
  return data;
}


static int LoadObjAndConvert(float bmin[3], float bmax[3], const char* filename)
{
  tinyobj_attrib_t attrib;
  tinyobj_shape_t  *shapes;
  size_t num_shapes;
  
  size_t data_len = 0;
  const char* data = get_file_data(&data_len, filename);
  if (data == NULL) {
    exit(-1);
    return 0;
  }
  printf("filesize: %d\n", (int)data_len);
  
  {
    int ret = tinyobj_parse(&attrib, shapes, &num_shapes, data, data_len);
  }

#if 0
  bmin[0] = bmin[1] = bmin[2] = std::numeric_limits<float>::max();
  bmax[0] = bmax[1] = bmax[2] = -std::numeric_limits<float>::max();

  {
        DrawObject o;
        std::vector<float> vb; // pos(3float), normal(3float), color(3float)
        size_t face_offset = 0;
        for (size_t v = 0; v < attrib.face_num_verts.size(); v++) {
          assert(attrib.face_num_verts[v] % 3 == 0); // assume all triangle face.
          for (size_t f = 0; f < attrib.face_num_verts[v] / 3; f++) {
            tinyobj_opt::vertex_index idx0 = attrib.faces[face_offset+3*f+0];
            tinyobj_opt::vertex_index idx1 = attrib.faces[face_offset+3*f+1];
            tinyobj_opt::vertex_index idx2 = attrib.faces[face_offset+3*f+2];

            float v[3][3];
            for (int k = 0; k < 3; k++) {
              int f0 = idx0.v_idx;
              int f1 = idx1.v_idx;
              int f2 = idx2.v_idx;
              assert(f0 >= 0);
              assert(f1 >= 0);
              assert(f2 >= 0);

              v[0][k] = attrib.vertices[3*f0+k];
              v[1][k] = attrib.vertices[3*f1+k];
              v[2][k] = attrib.vertices[3*f2+k];
              bmin[k] = std::min(v[0][k], bmin[k]);
              bmin[k] = std::min(v[1][k], bmin[k]);
              bmin[k] = std::min(v[2][k], bmin[k]);
              bmax[k] = std::max(v[0][k], bmax[k]);
              bmax[k] = std::max(v[1][k], bmax[k]);
              bmax[k] = std::max(v[2][k], bmax[k]);
            }

            float n[3][3];

            if (attrib.normals.size() > 0) { 
              int f0 = idx0.vn_idx;
              int f1 = idx1.vn_idx;
              int f2 = idx2.vn_idx;
              assert(f0 >= 0);
              assert(f1 >= 0);
              assert(f2 >= 0);
              assert(3*f0+2 < attrib.normals.size());
              assert(3*f1+2 < attrib.normals.size());
              assert(3*f2+2 < attrib.normals.size());
              for (int k = 0; k < 3; k++) {
                n[0][k] = attrib.normals[3*f0+k];
                n[1][k] = attrib.normals[3*f1+k];
                n[2][k] = attrib.normals[3*f2+k];
              }
            } else {
              // compute geometric normal
              CalcNormal(n[0], v[0], v[1], v[2]);
              n[1][0] = n[0][0]; n[1][1] = n[0][1]; n[1][2] = n[0][2];
              n[2][0] = n[0][0]; n[2][1] = n[0][1]; n[2][2] = n[0][2];
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
          face_offset += attrib.face_num_verts[v];
        }

        o.vb = 0;
        o.numTriangles = 0;
        if (vb.size() > 0) {
          glGenBuffers(1, &o.vb);
          glBindBuffer(GL_ARRAY_BUFFER, o.vb);
          glBufferData(GL_ARRAY_BUFFER, vb.size() * sizeof(float), &vb.at(0), GL_STATIC_DRAW);
          o.numTriangles = vb.size() / 9 / 3;
        }

        gDrawObjects.push_back(o);
  }
  
  printf("bmin = %f, %f, %f\n", bmin[0], bmin[1], bmin[2]);
  printf("bmax = %f, %f, %f\n", bmax[0], bmax[1], bmax[2]);

  return 1;
#else
  return 0;
#endif
}

static void reshapeFunc(GLFWwindow* window, int w, int h)
{
  int fb_w, fb_h;
  glfwGetFramebufferSize(window, &fb_w, &fb_h);

  glViewport(0, 0, fb_w, fb_h);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  gluPerspective(45.0, (GLdouble)w / (GLdouble)h, (GLdouble)0.01f, (GLdouble)100.0f);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity();

  width = w;
  height = h;
}

static void keyboardFunc(GLFWwindow *window, int key, int scancode, int action, int mods) {
  (void)window;
  (void)scancode;
  (void)mods;
    if(action == GLFW_PRESS || action == GLFW_REPEAT){
        /* Move camera */
        float mv_x = 0, mv_y = 0, mv_z = 0;
        if(key == GLFW_KEY_K) mv_x += 1;
        else if(key == GLFW_KEY_J) mv_x += -1;
        else if(key == GLFW_KEY_L) mv_y += 1;
        else if(key == GLFW_KEY_H) mv_y += -1;
        else if(key == GLFW_KEY_P) mv_z += 1;
        else if(key == GLFW_KEY_N) mv_z += -1;

        if(key == GLFW_KEY_Q || key == GLFW_KEY_ESCAPE) glfwSetWindowShouldClose(window, GL_TRUE);
    }
}

static void clickFunc(GLFWwindow* window, int button, int action, int mods){
  (void)window;
  (void)mods;
    if(button == GLFW_MOUSE_BUTTON_LEFT){
        if(action == GLFW_PRESS){
            mouseLeftPressed = 1;
            trackball(prev_quat, 0.0, 0.0, 0.0, 0.0);
        } else if(action == GLFW_RELEASE){
            mouseLeftPressed = 0;
        }
    }
    if(button == GLFW_MOUSE_BUTTON_RIGHT){
        if(action == GLFW_PRESS){
            mouseRightPressed = 1;
        } else if(action == GLFW_RELEASE){
            mouseRightPressed = 0;
        }
    }
    if(button == GLFW_MOUSE_BUTTON_MIDDLE){
        if(action == GLFW_PRESS){
            mouseMiddlePressed = 1;
        } else if(action == GLFW_RELEASE){
            mouseMiddlePressed = 0;
        }
    }
}

static void motionFunc(GLFWwindow* window, double mouse_x, double mouse_y){
  float rotScale = 1.0f;
  float transScale = 2.0f;

  (void)window;

    if(mouseLeftPressed){
      trackball(prev_quat,
          rotScale * (2.0f * prevMouseX - width) / (float)width,
          rotScale * (height - 2.0f * prevMouseY) / (float)height,
          rotScale * (2.0f * (float)mouse_x - width) / (float)width,
          rotScale * (height - 2.0f * (float)mouse_y) / (float)height);

      add_quats(prev_quat, curr_quat, curr_quat);
    } else if (mouseMiddlePressed) {
      eye[0] -= transScale * ((float)mouse_x - prevMouseX) / (float)width;
      lookat[0] -= transScale * ((float)mouse_x - prevMouseX) / (float)width;
      eye[1] += transScale * ((float)mouse_y - prevMouseY) / (float)height;
      lookat[1] += transScale * ((float)mouse_y - prevMouseY) / (float)height;
    } else if (mouseRightPressed) {
      eye[2] += transScale * ((float)mouse_y - prevMouseY) / (float)height;
      lookat[2] += transScale * ((float)mouse_y - prevMouseY) / (float)height;
    }

    prevMouseX = (float)mouse_x;
    prevMouseY = (float)mouse_y;
}

static void Draw(const DrawObject* draw_objects, int num_draw_objects)
{
  int i;

  glPolygonMode(GL_FRONT, GL_FILL);
  glPolygonMode(GL_BACK, GL_FILL);

  glEnable(GL_POLYGON_OFFSET_FILL);
  glPolygonOffset(1.0, 1.0);
  glColor3f(1.0f, 1.0f, 1.0f);
  for (i = 0; i < num_draw_objects; i++) {
    const DrawObject o = draw_objects[i];
    if (o.vb < 1) {
      continue;
    }
 
    glBindBuffer(GL_ARRAY_BUFFER, o.vb);
    glEnableClientState(GL_VERTEX_ARRAY);
    glEnableClientState(GL_NORMAL_ARRAY);
    glEnableClientState(GL_COLOR_ARRAY);
    glVertexPointer(3, GL_FLOAT, 36, (const void*)0);
    glNormalPointer(GL_FLOAT, 36, (const void*)(sizeof(float)*3));
    glColorPointer(3, GL_FLOAT, 36, (const void*)(sizeof(float)*6));

    glDrawArrays(GL_TRIANGLES, 0, 3 * o.numTriangles);
    CheckErrors("drawarrays");
  }

  /* draw wireframe */
  glDisable(GL_POLYGON_OFFSET_FILL);
  glPolygonMode(GL_FRONT, GL_LINE);
  glPolygonMode(GL_BACK, GL_LINE);

  glColor3f(0.0f, 0.0f, 0.4f);
  for (i = 0; i < num_draw_objects; i++) {
    DrawObject o = draw_objects[i];
    if (o.vb < 1) {
      continue;
    }
 
    glBindBuffer(GL_ARRAY_BUFFER, o.vb);
    glEnableClientState(GL_VERTEX_ARRAY);
    glEnableClientState(GL_NORMAL_ARRAY);
    glDisableClientState(GL_COLOR_ARRAY);
    glVertexPointer(3, GL_FLOAT, 36, (const void*)0);
    glNormalPointer(GL_FLOAT, 36, (const void*)(sizeof(float)*3));

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


int main(int argc, char **argv)
{
  if (argc < 2) {
    fprintf(stderr, "Needs input.obj\n");
    return 0;
  }

  Init();

  printf("Initialize GLFW...\n");

  if(!glfwInit()){
    fprintf(stderr, "Failed to initialize GLFW.\n");
    return -1;
  }

  gWindow = glfwCreateWindow(width, height, "Obj viewer", NULL, NULL);
  if(gWindow == NULL){
    fprintf(stderr, "Failed to open GLFW window.\n");
    glfwTerminate();
    return 1;
  }

  glfwMakeContextCurrent(gWindow);
  glfwSwapInterval(1);

  glfwSetWindowSizeCallback(gWindow, reshapeFunc);
  glfwSetKeyCallback(gWindow, keyboardFunc);
  glfwSetMouseButtonCallback(gWindow, clickFunc);
  glfwSetCursorPosCallback(gWindow, motionFunc);

  /* glewExperimental = 1; */
  if (glewInit() != GLEW_OK) {
    fprintf(stderr, "Failed to initialize GLEW.\n");
    return -1;
  }

  reshapeFunc(gWindow, width, height);

  {
    float bmin[3], bmax[3];
    float maxExtent;
    if (0 == LoadObjAndConvert(bmin, bmax, argv[1])) {
      printf("failed to load & conv\n");
      return -1;
    }

    maxExtent = 0.5f * (bmax[0] - bmin[0]);
    if (maxExtent < 0.5f * (bmax[1] - bmin[1])) {
      maxExtent = 0.5f * (bmax[1] - bmin[1]);
    }
    if (maxExtent < 0.5f * (bmax[2] - bmin[2])) {
      maxExtent = 0.5f * (bmax[2] - bmin[2]);
    }

	  while(glfwWindowShouldClose(gWindow) == GL_FALSE) {
	    GLfloat mat[4][4];

	    glfwPollEvents();
	    glClearColor(0.1f, 0.2f, 0.3f, 1.0f);
	    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

	    glEnable(GL_DEPTH_TEST);

	    glMatrixMode(GL_MODELVIEW);
	    glLoadIdentity();
	    gluLookAt((GLdouble)eye[0], (GLdouble)eye[1], (GLdouble)eye[2], (GLdouble)lookat[0], (GLdouble)lookat[1], (GLdouble)lookat[2], (GLdouble)up[0], (GLdouble)up[1], (GLdouble)up[2]);
	    build_rotmatrix(mat, curr_quat);
	    glMultMatrixf(&mat[0][0]);

	    /* Fit to -1, 1 */
	    glScalef(1.0f / maxExtent, 1.0f / maxExtent, 1.0f / maxExtent);

	    /* Centerize object. */
	    glTranslatef(-0.5f*(bmax[0] + bmin[0]), -0.5f*(bmax[1] + bmin[1]), -0.5f*(bmax[2] + bmin[2]));
	  
	    Draw(gDrawObjects, gNumDrawObjects);

	    glfwSwapBuffers(gWindow);
	  }

  }

  glfwTerminate();
}
