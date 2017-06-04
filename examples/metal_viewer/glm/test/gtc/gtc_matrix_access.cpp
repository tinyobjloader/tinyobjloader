///////////////////////////////////////////////////////////////////////////////////
/// OpenGL Mathematics (glm.g-truc.net)
///
/// Copyright (c) 2005 - 2015 G-Truc Creation (www.g-truc.net)
/// Permission is hereby granted, free of charge, to any person obtaining a copy
/// of this software and associated documentation files (the "Software"), to deal
/// in the Software without restriction, including without limitation the rights
/// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
/// copies of the Software, and to permit persons to whom the Software is
/// furnished to do so, subject to the following conditions:
/// 
/// The above copyright notice and this permission notice shall be included in
/// all copies or substantial portions of the Software.
/// 
/// Restrictions:
///		By making use of the Software for military purposes, you choose to make
///		a Bunny unhappy.
/// 
/// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
/// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
/// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
/// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
/// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
/// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
/// THE SOFTWARE.
///
/// @file test/gtc/gtc_matrix_access.cpp
/// @date 2010-09-16 / 2014-11-25
/// @author Christophe Riccio
///////////////////////////////////////////////////////////////////////////////////

#include <glm/gtc/matrix_access.hpp>
#include <glm/mat2x2.hpp>
#include <glm/mat2x3.hpp>
#include <glm/mat2x4.hpp>
#include <glm/mat3x2.hpp>
#include <glm/mat3x3.hpp>
#include <glm/mat3x4.hpp>
#include <glm/mat4x2.hpp>
#include <glm/mat4x3.hpp>
#include <glm/mat4x4.hpp>

int test_mat2x2_row_set()
{
	int Error = 0;

	glm::mat2x2 m(1);

	m = glm::row(m, 0, glm::vec2( 0,  1));
	m = glm::row(m, 1, glm::vec2( 4,  5));

	Error += glm::row(m, 0) == glm::vec2( 0,  1) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec2( 4,  5) ? 0 : 1;

	return Error;
}

int test_mat2x2_col_set()
{
	int Error = 0;

	glm::mat2x2 m(1);

	m = glm::column(m, 0, glm::vec2( 0,  1));
	m = glm::column(m, 1, glm::vec2( 4,  5));

	Error += glm::column(m, 0) == glm::vec2( 0,  1) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec2( 4,  5) ? 0 : 1;

	return Error;
}

int test_mat2x3_row_set()
{
	int Error = 0;

	glm::mat2x3 m(1);

	m = glm::row(m, 0, glm::vec2( 0,  1));
	m = glm::row(m, 1, glm::vec2( 4,  5));
	m = glm::row(m, 2, glm::vec2( 8,  9));

	Error += glm::row(m, 0) == glm::vec2( 0,  1) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec2( 4,  5) ? 0 : 1;
	Error += glm::row(m, 2) == glm::vec2( 8,  9) ? 0 : 1;

	return Error;
}

int test_mat2x3_col_set()
{
	int Error = 0;

	glm::mat2x3 m(1);

	m = glm::column(m, 0, glm::vec3( 0,  1,  2));
	m = glm::column(m, 1, glm::vec3( 4,  5,  6));

	Error += glm::column(m, 0) == glm::vec3( 0,  1,  2) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec3( 4,  5,  6) ? 0 : 1;

	return Error;
}

int test_mat2x4_row_set()
{
	int Error = 0;

	glm::mat2x4 m(1);

	m = glm::row(m, 0, glm::vec2( 0,  1));
	m = glm::row(m, 1, glm::vec2( 4,  5));
	m = glm::row(m, 2, glm::vec2( 8,  9));
	m = glm::row(m, 3, glm::vec2(12, 13));

	Error += glm::row(m, 0) == glm::vec2( 0,  1) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec2( 4,  5) ? 0 : 1;
	Error += glm::row(m, 2) == glm::vec2( 8,  9) ? 0 : 1;
	Error += glm::row(m, 3) == glm::vec2(12, 13) ? 0 : 1;

	return Error;
}

int test_mat2x4_col_set()
{
	int Error = 0;

	glm::mat2x4 m(1);

	m = glm::column(m, 0, glm::vec4( 0,  1,  2, 3));
	m = glm::column(m, 1, glm::vec4( 4,  5,  6, 7));

	Error += glm::column(m, 0) == glm::vec4( 0,  1,  2, 3) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec4( 4,  5,  6, 7) ? 0 : 1;

	return Error;
}

int test_mat3x2_row_set()
{
	int Error = 0;

	glm::mat3x2 m(1);

	m = glm::row(m, 0, glm::vec3( 0,  1,  2));
	m = glm::row(m, 1, glm::vec3( 4,  5,  6));

	Error += glm::row(m, 0) == glm::vec3( 0,  1,  2) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec3( 4,  5,  6) ? 0 : 1;

	return Error;
}

int test_mat3x2_col_set()
{
	int Error = 0;

	glm::mat3x2 m(1);

	m = glm::column(m, 0, glm::vec2( 0,  1));
	m = glm::column(m, 1, glm::vec2( 4,  5));
	m = glm::column(m, 2, glm::vec2( 8,  9));

	Error += glm::column(m, 0) == glm::vec2( 0,  1) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec2( 4,  5) ? 0 : 1;
	Error += glm::column(m, 2) == glm::vec2( 8,  9) ? 0 : 1;

	return Error;
}

int test_mat3x3_row_set()
{
	int Error = 0;

	glm::mat3x3 m(1);

	m = glm::row(m, 0, glm::vec3( 0,  1,  2));
	m = glm::row(m, 1, glm::vec3( 4,  5,  6));
	m = glm::row(m, 2, glm::vec3( 8,  9, 10));

	Error += glm::row(m, 0) == glm::vec3( 0,  1,  2) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec3( 4,  5,  6) ? 0 : 1;
	Error += glm::row(m, 2) == glm::vec3( 8,  9, 10) ? 0 : 1;

	return Error;
}

int test_mat3x3_col_set()
{
	int Error = 0;

	glm::mat3x3 m(1);

	m = glm::column(m, 0, glm::vec3( 0,  1,  2));
	m = glm::column(m, 1, glm::vec3( 4,  5,  6));
	m = glm::column(m, 2, glm::vec3( 8,  9, 10));

	Error += glm::column(m, 0) == glm::vec3( 0,  1,  2) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec3( 4,  5,  6) ? 0 : 1;
	Error += glm::column(m, 2) == glm::vec3( 8,  9, 10) ? 0 : 1;

	return Error;
}

int test_mat3x4_row_set()
{
	int Error = 0;

	glm::mat3x4 m(1);

	m = glm::row(m, 0, glm::vec3( 0,  1,  2));
	m = glm::row(m, 1, glm::vec3( 4,  5,  6));
	m = glm::row(m, 2, glm::vec3( 8,  9, 10));
	m = glm::row(m, 3, glm::vec3(12, 13, 14));

	Error += glm::row(m, 0) == glm::vec3( 0,  1,  2) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec3( 4,  5,  6) ? 0 : 1;
	Error += glm::row(m, 2) == glm::vec3( 8,  9, 10) ? 0 : 1;
	Error += glm::row(m, 3) == glm::vec3(12, 13, 14) ? 0 : 1;

	return Error;
}

int test_mat3x4_col_set()
{
	int Error = 0;

	glm::mat3x4 m(1);

	m = glm::column(m, 0, glm::vec4( 0,  1,  2, 3));
	m = glm::column(m, 1, glm::vec4( 4,  5,  6, 7));
	m = glm::column(m, 2, glm::vec4( 8,  9, 10, 11));

	Error += glm::column(m, 0) == glm::vec4( 0,  1,  2, 3) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec4( 4,  5,  6, 7) ? 0 : 1;
	Error += glm::column(m, 2) == glm::vec4( 8,  9, 10, 11) ? 0 : 1;

	return Error;
}

int test_mat4x2_row_set()
{
	int Error = 0;

	glm::mat4x2 m(1);

	m = glm::row(m, 0, glm::vec4( 0,  1,  2,  3));
	m = glm::row(m, 1, glm::vec4( 4,  5,  6,  7));

	Error += glm::row(m, 0) == glm::vec4( 0,  1,  2,  3) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec4( 4,  5,  6,  7) ? 0 : 1;

	return Error;
}

int test_mat4x2_col_set()
{
	int Error = 0;

	glm::mat4x2 m(1);

	m = glm::column(m, 0, glm::vec2( 0,  1));
	m = glm::column(m, 1, glm::vec2( 4,  5));
	m = glm::column(m, 2, glm::vec2( 8,  9));
	m = glm::column(m, 3, glm::vec2(12, 13));

	Error += glm::column(m, 0) == glm::vec2( 0,  1) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec2( 4,  5) ? 0 : 1;
	Error += glm::column(m, 2) == glm::vec2( 8,  9) ? 0 : 1;
	Error += glm::column(m, 3) == glm::vec2(12, 13) ? 0 : 1;

	return Error;
}

int test_mat4x3_row_set()
{
	int Error = 0;

	glm::mat4x3 m(1);

	m = glm::row(m, 0, glm::vec4( 0,  1,  2,  3));
	m = glm::row(m, 1, glm::vec4( 4,  5,  6,  7));
	m = glm::row(m, 2, glm::vec4( 8,  9, 10, 11));

	Error += glm::row(m, 0) == glm::vec4( 0,  1,  2,  3) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec4( 4,  5,  6,  7) ? 0 : 1;
	Error += glm::row(m, 2) == glm::vec4( 8,  9, 10, 11) ? 0 : 1;

	return Error;
}

int test_mat4x3_col_set()
{
	int Error = 0;

	glm::mat4x3 m(1);

	m = glm::column(m, 0, glm::vec3( 0,  1,  2));
	m = glm::column(m, 1, glm::vec3( 4,  5,  6));
	m = glm::column(m, 2, glm::vec3( 8,  9, 10));
	m = glm::column(m, 3, glm::vec3(12, 13, 14));

	Error += glm::column(m, 0) == glm::vec3( 0,  1,  2) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec3( 4,  5,  6) ? 0 : 1;
	Error += glm::column(m, 2) == glm::vec3( 8,  9, 10) ? 0 : 1;
	Error += glm::column(m, 3) == glm::vec3(12, 13, 14) ? 0 : 1;

	return Error;
}

int test_mat4x4_row_set()
{
	int Error = 0;

	glm::mat4 m(1);

	m = glm::row(m, 0, glm::vec4( 0,  1,  2,  3));
	m = glm::row(m, 1, glm::vec4( 4,  5,  6,  7));
	m = glm::row(m, 2, glm::vec4( 8,  9, 10, 11));
	m = glm::row(m, 3, glm::vec4(12, 13, 14, 15));

	Error += glm::row(m, 0) == glm::vec4( 0,  1,  2,  3) ? 0 : 1;
	Error += glm::row(m, 1) == glm::vec4( 4,  5,  6,  7) ? 0 : 1;
	Error += glm::row(m, 2) == glm::vec4( 8,  9, 10, 11) ? 0 : 1;
	Error += glm::row(m, 3) == glm::vec4(12, 13, 14, 15) ? 0 : 1;

	return Error;
}

int test_mat4x4_col_set()
{
	int Error = 0;

	glm::mat4 m(1);

	m = glm::column(m, 0, glm::vec4( 0,  1,  2,  3));
	m = glm::column(m, 1, glm::vec4( 4,  5,  6,  7));
	m = glm::column(m, 2, glm::vec4( 8,  9, 10, 11));
	m = glm::column(m, 3, glm::vec4(12, 13, 14, 15));

	Error += glm::column(m, 0) == glm::vec4( 0,  1,  2,  3) ? 0 : 1;
	Error += glm::column(m, 1) == glm::vec4( 4,  5,  6,  7) ? 0 : 1;
	Error += glm::column(m, 2) == glm::vec4( 8,  9, 10, 11) ? 0 : 1;
	Error += glm::column(m, 3) == glm::vec4(12, 13, 14, 15) ? 0 : 1;

	return Error;
}

int test_mat4x4_row_get()
{
	int Error = 0;

	glm::mat4 m(1);

	glm::vec4 A = glm::row(m, 0);
	Error += A == glm::vec4(1, 0, 0, 0) ? 0 : 1;
	glm::vec4 B = glm::row(m, 1);
	Error += B == glm::vec4(0, 1, 0, 0) ? 0 : 1;
	glm::vec4 C = glm::row(m, 2);
	Error += C == glm::vec4(0, 0, 1, 0) ? 0 : 1;
	glm::vec4 D = glm::row(m, 3);
	Error += D == glm::vec4(0, 0, 0, 1) ? 0 : 1;

	return Error;
}

int test_mat4x4_col_get()
{
	int Error = 0;

	glm::mat4 m(1);

	glm::vec4 A = glm::column(m, 0);
	Error += A == glm::vec4(1, 0, 0, 0) ? 0 : 1;
	glm::vec4 B = glm::column(m, 1);
	Error += B == glm::vec4(0, 1, 0, 0) ? 0 : 1;
	glm::vec4 C = glm::column(m, 2);
	Error += C == glm::vec4(0, 0, 1, 0) ? 0 : 1;
	glm::vec4 D = glm::column(m, 3);
	Error += D == glm::vec4(0, 0, 0, 1) ? 0 : 1;

	return Error;
}

int main()
{
	int Error = 0;

	Error += test_mat2x2_row_set();
	Error += test_mat2x2_col_set();
	Error += test_mat2x3_row_set();
	Error += test_mat2x3_col_set();
	Error += test_mat2x4_row_set();
	Error += test_mat2x4_col_set();
	Error += test_mat3x2_row_set();
	Error += test_mat3x2_col_set();
	Error += test_mat3x3_row_set();
	Error += test_mat3x3_col_set();
	Error += test_mat3x4_row_set();
	Error += test_mat3x4_col_set();
	Error += test_mat4x2_row_set();
	Error += test_mat4x2_col_set();
	Error += test_mat4x3_row_set();
	Error += test_mat4x3_col_set();
	Error += test_mat4x4_row_set();
	Error += test_mat4x4_col_set();

	Error += test_mat4x4_row_get();
	Error += test_mat4x4_col_get();

	return Error;
}
