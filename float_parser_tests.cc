#include <cstdio>
#include <cstddef>
#include <cstring>
#include <cmath>
#include <cctype>

// Tries to parse a floating point number located at s.
//
// s_end should be a location in the string where reading should absolutely
// stop. For example at the end of the string, to prevent buffer overflows.
//
// Parses the following EBNF grammar:
//   sign    = "+" | "-" ;
//   END     = ? anything not in digit ?
//   digit   = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
//   integer = [sign] , digit , {digit} ;
//   decimal = integer , ["." , integer] ;
//   float   = ( decimal , END ) | ( decimal , ("E" | "e") , integer , END ) ;
//
//  Valid strings are for example:
//   -0	 +3.1417e+2  -0.0E-3  1.0324  -1.41   11e2
//
// If the parsing is a success, result is set to the parsed value and true 
// is returned.
//
// The function is greedy and will parse until any of the following happens:
//  - a non-conforming character is encountered.
//  - s_end is reached.
//
// The following situations triggers a failure:
//  - s >= s_end.
//  - parse failure.
// 
bool tryParseDouble(const char *s, const char *s_end, double *result)
{
	if (s >= s_end)
	{
		return false;
	}

	double mantissa = 0.0;
	// This exponent is base 2 rather than 10.
	// However the exponent we parse is supposed to be one of ten,
	// thus we must take care to convert the exponent/and or the 
	// mantissa to a * 2^E, where a is the mantissa and E is the
	// exponent.
	// To get the final double we will use ldexp, it requires the
	// exponent to be in base 2.
	int exponent = 0;

	// NOTE: THESE MUST BE DECLARED HERE SINCE WE ARE NOT ALLOWED
	// TO JUMP OVER DEFINITIONS.
	char sign = '+';
	char exp_sign = '+';
	char const *curr = s;

	// How many characters were read in a loop. 
	int read = 0;
	// Tells whether a loop terminated due to reaching s_end.
	bool end_not_reached = false;

	/*
		BEGIN PARSING.
	*/

	// Find out what sign we've got.
	if (*curr == '+' || *curr == '-')
	{
		sign = *curr;
		curr++;
	}
	else if (isdigit(*curr)) { /* Pass through. */ }
	else
	{
		goto fail;
	}

	// Read the integer part.
	while ((end_not_reached = (curr != s_end)) && isdigit(*curr))
	{
		mantissa *= 10;
		mantissa += static_cast<int>(*curr - 0x30);
		curr++;	read++;
	}

	// We must make sure we actually got something.
	if (read == 0)
		goto fail;
	// We allow numbers of form "#", "###" etc.
	if (!end_not_reached)
		goto assemble;

	// Read the decimal part.
	if (*curr == '.')
	{
		curr++;
		read = 1;
		while ((end_not_reached = (curr != s_end)) && isdigit(*curr))
		{
			// NOTE: Don't use powf here, it will absolutely murder precision.
			mantissa += static_cast<int>(*curr - 0x30) * pow(10, -read);
			read++; curr++;
		}
	}
	else if (*curr == 'e' || *curr == 'E') {}
	else
	{
		goto assemble;
	}

	if (!end_not_reached)
		goto assemble;

	// Read the exponent part.
	if (*curr == 'e' || *curr == 'E')
	{
		curr++;
		// Figure out if a sign is present and if it is.
		if ((end_not_reached = (curr != s_end)) && (*curr == '+' || *curr == '-'))
		{
			exp_sign = *curr;
			curr++;
		}
		else if (isdigit(*curr)) { /* Pass through. */ }
		else
		{
			// Empty E is not allowed.
			goto fail;
		}

		read = 0;
		while ((end_not_reached = (curr != s_end)) && isdigit(*curr))
		{
			exponent *= 10;
			exponent += static_cast<int>(*curr - 0x30);
			curr++;	read++;
		}
		exponent *= (exp_sign == '+'? 1 : -1);
		if (read == 0)
			goto fail;
	}

assemble:
	*result = (sign == '+'? 1 : -1) * ldexp(mantissa * pow(5, exponent), exponent);
	return true;
fail:
	return false;
}

void testParsing(const char *input, bool expectedRes, double expectedValue)
{
	double val = 0.0;
	bool res = tryParseDouble(input, input + strlen(input), &val);
	if (res != expectedRes || fabs(val - expectedValue) > 0.000001)
	{
		printf("% 20s failed, returned %d and value % 10.5f.\n\t\tExpected value was % 10.5f\n------\n", input, res, val, expectedValue);
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
	testParsing("34.0E-2\04", true, 34.0e-2);
	testParsing("+34.23E2\032", true, 34.23E2);
	testParsing("10.023", true, 10.023);
	testParsing("1.0e+23", true, 1.e+23);
	testParsing("10e+23", true, 10e+23);
	testParsing("20301.000", true, 20301.000);
	testParsing("-41044.000", true, -41044.000);
	testParsing("-93558.000", true, -93558.000);
	testParsing("-79620.000", true, -79620.000);
	testParsing("5257.000", true, 5257.000);
	testParsing("-7145.000", true, -7145.000);
	testParsing("-77314.000", true, -77314.000);
	testParsing("-27131.000", true, -27131.000);
	testParsing("52744.000", true, 52744.000);
	testParsing("48106.000", true, 48106.000);
	testParsing("42939.000", true, 42939.000);
	testParsing("41187.000", true, 41187.000);
	testParsing("70851.000", true, 70851.000);
	testParsing("-90431.000", true, -90431.000);
	testParsing("-13564.000", true, -13564.000);
	testParsing("27150.000", true, 27150.000);
	testParsing("71992.000", true, 71992.000);
	testParsing("-42845.000", true, -42845.000);
	testParsing("24806.000", true, 24806.000);
	testParsing("30753.000", true, 30753.000);
	testParsing("1.658500e+04", true, 1.658500e+04);
	testParsing("9.572500e+04", true, 9.572500e+04);
	testParsing("-5.888600e+04", true, -5.888600e+04);
	testParsing("-2.998000e+04", true, -2.998000e+04);
	testParsing("-4.842700e+04", true, -4.842700e+04);
	testParsing("9.575400e+04", true, 9.575400e+04);
	testParsing("-8.311500e+04", true, -8.311500e+04);
	testParsing("-3.770800e+04", true, -3.770800e+04);
	testParsing("-3.141600e+04", true, -3.141600e+04);
	testParsing("-4.673700e+04", true, -4.673700e+04);
	testParsing("-5.112400e+04", true, -5.112400e+04);
	testParsing("7.111000e+03", true, 7.111000e+03);
	testParsing("-3.727000e+03", true, -3.727000e+03);
	testParsing("6.940700e+04", true, 6.940700e+04);
	testParsing("-3.635100e+04", true, -3.635100e+04);
	testParsing("2.762100e+04", true, 2.762100e+04);
	testParsing("-1.512600e+04", true, -1.512600e+04);
	testParsing("3.338000e+03", true, 3.338000e+03);
	testParsing("7.598100e+04", true, 7.598100e+04);
	testParsing("-8.198400e+04", true, -8.198400e+04);
	testParsing("-", false, 0.0);
	testParsing(" +", false, 0.0);
	testParsing("", false, 0.0);
	testParsing(".232", false, 0.0);
	testParsing(".232E2", false, 0.0);
	testParsing(".232", false, 0.0);
	testParsing(".", false, 0.0);
	testParsing(".E", false, 0.0);
	testParsing("233.E", false, 0.0);
	testParsing("233.323E-", false, 0.0);
	testParsing("233.323E+", false, 0.0);




	return 0;
}