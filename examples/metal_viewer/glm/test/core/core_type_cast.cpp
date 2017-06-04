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
/// @file test/core/core_type_cast.cpp
/// @date 2013-05-06 / 2014-11-25
/// @author Christophe Riccio
///////////////////////////////////////////////////////////////////////////////////

#include <glm/glm.hpp>
#include <algorithm>
#include <vector>
#include <iterator>

struct my_vec2
{
	operator glm::vec2() { return glm::vec2(x, y); }
	float x, y;
};

int test_vec2_cast()
{
	glm::vec2 A(1.0f, 2.0f);
	glm::lowp_vec2 B(A);
	glm::mediump_vec2 C(A);
	glm::highp_vec2 D(A);
	
	glm::vec2 E = static_cast<glm::vec2>(A);
	glm::lowp_vec2 F = static_cast<glm::lowp_vec2>(A);
	glm::mediump_vec2 G = static_cast<glm::mediump_vec2>(A);
	glm::highp_vec2 H = static_cast<glm::highp_vec2>(A);
	
	my_vec2 I;
	glm::vec2 J = static_cast<glm::vec2>(I);
	glm::vec2 K(7.8f);

	int Error(0);
	
	Error += glm::all(glm::equal(A, E)) ? 0 : 1;
	Error += glm::all(glm::equal(B, F)) ? 0 : 1;
	Error += glm::all(glm::equal(C, G)) ? 0 : 1;
	Error += glm::all(glm::equal(D, H)) ? 0 : 1;
	
	return Error;
}

int test_vec3_cast()
{
	glm::vec3 A(1.0f, 2.0f, 3.0f);
	glm::lowp_vec3 B(A);
	glm::mediump_vec3 C(A);
	glm::highp_vec3 D(A);
	
	glm::vec3 E = static_cast<glm::vec3>(A);
	glm::lowp_vec3 F = static_cast<glm::lowp_vec3>(A);
	glm::mediump_vec3 G = static_cast<glm::mediump_vec3>(A);
	glm::highp_vec3 H = static_cast<glm::highp_vec3>(A);
	
	int Error(0);
	
	Error += glm::all(glm::equal(A, E)) ? 0 : 1;
	Error += glm::all(glm::equal(B, F)) ? 0 : 1;
	Error += glm::all(glm::equal(C, G)) ? 0 : 1;
	Error += glm::all(glm::equal(D, H)) ? 0 : 1;
	
	return Error;
}

int test_vec4_cast()
{
	glm::vec4 A(1.0f, 2.0f, 3.0f, 4.0f);
	glm::lowp_vec4 B(A);
	glm::mediump_vec4 C(A);
	glm::highp_vec4 D(A);
	
	glm::vec4 E = static_cast<glm::vec4>(A);
	glm::lowp_vec4 F = static_cast<glm::lowp_vec4>(A);
	glm::mediump_vec4 G = static_cast<glm::mediump_vec4>(A);
	glm::highp_vec4 H = static_cast<glm::highp_vec4>(A);
	
	int Error(0);
	
	Error += glm::all(glm::equal(A, E)) ? 0 : 1;
	Error += glm::all(glm::equal(B, F)) ? 0 : 1;
	Error += glm::all(glm::equal(C, G)) ? 0 : 1;
	Error += glm::all(glm::equal(D, H)) ? 0 : 1;
	
	return Error;
}

int test_std_copy()
{
	int Error = 0;

	{
		std::vector<int> High;
		High.resize(64);
		std::vector<int> Medium(High.size());
		
		std::copy(High.begin(), High.end(), Medium.begin());

		*Medium.begin() = *High.begin();
	}

	{
		std::vector<glm::dvec4> High4;
		High4.resize(64);
		std::vector<glm::vec4> Medium4(High4.size());
		
		std::copy(High4.begin(), High4.end(), Medium4.begin());

		*Medium4.begin() = *High4.begin();
	}

	{
		std::vector<glm::dvec3> High3;
		High3.resize(64);
		std::vector<glm::vec3> Medium3(High3.size());

		std::copy(High3.begin(), High3.end(), Medium3.begin());

		*Medium3.begin() = *High3.begin();
	}

	{
		std::vector<glm::dvec2> High2;
		High2.resize(64);
		std::vector<glm::vec2> Medium2(High2.size());

		std::copy(High2.begin(), High2.end(), Medium2.begin());

		*Medium2.begin() = *High2.begin();
	}

	glm::dvec4 v1;
	glm::vec4 v2;

	v2 = v1;

	return Error;
}

int main()
{
	int Error = 0;

	Error += test_std_copy();
	Error += test_vec2_cast();
	Error += test_vec3_cast();
	Error += test_vec4_cast();

	return Error;
}
