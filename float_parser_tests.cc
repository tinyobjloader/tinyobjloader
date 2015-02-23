#include <cstdio>
#include <cstddef>

// Tries to parse a floating point number located at s.
//
// Parses the following EBNF grammar:
//   sign    = "+" | "-" ;
//   END     = ? anything not in digit ?
//   digit   = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
//   integer = [sign] , digit , {digit} ;
//   decimal = integer , ["." , {digit}] ;
//   float   = ( decimal , END ) | ( decimal , ("E" | "e") , decimal , END ) ;
//
//  Valid strings are for example:
//   -0	 +3.1417e+2  -0.E-3  1.0324  -1.41   11e2
//
// If the parsing is a success, result is set to the parsed value and true 
// is returned.
//
// The function is greedy, it will parse until it encounters a null-byte or
// a non-conforming character is encountered.
//
// The following situations triggers a failure:
//  - parse failure.
//  - underflow/overflow.
// 
bool tryParseFloat(const char *s, double *result)
{
	return false;
}

void testParsing(const char *input, bool expectedRes, double expectedValue)
{
	double val = 0.0;
	bool res = tryParseFloat(input, &val);
	if (res != expectedRes || val != expectedValue)
	{
		printf("% 20s failed, returned %d and value % 10.4f.\n", input, res, val);
	}
}

int main(int argc, char const *argv[])
{
	testParsing("0",  true,  0.0);
	testParsing("-0", true,  0.0);
	testParsing("+0", true,  0.0);
	testParsing("1",  true,  1.0);
	testParsing("+1", true,  1.0);
	testParsing("-1", true, -1.0);
	testParsing("-1.08", true, -1.08);
	testParsing("100.0823blabla", true, 100.0823);
	testParsing("34.E-2\04", true, 34.0e-2);
	testParsing("+34.23E2\02", true, 34.23E2);
	return 0;
}