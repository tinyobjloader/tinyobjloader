#include "../tinyobj_v3.hh"
#include <cstdio>

int main() {
    const char* mtl_content =
        "newmtl test\n"
        "Pr 0.5\n"
        "Pm 0.3\n";

    tinyobj::v3::StreamReader reader(mtl_content, strlen(mtl_content));

    std::string line;
    while (reader.readLine(line, 1024)) {
        printf("Line: '%s'\n", line.c_str());

        tinyobj::v3::StreamReader line_reader(line.data(), line.size());

        std::string cmd;
        tinyobj::v3::detail::skipSpaces(line_reader);
        if (tinyobj::v3::detail::readWord(line_reader, cmd)) {
            printf("  Command: '%s'\n", cmd.c_str());

            if (cmd == "Pr") {
                float val;
                tinyobj::v3::detail::skipSpaces(line_reader);

                // Try manual parse
                char ch;
                if (line_reader.peekChar(ch)) {
                    printf("  Next char: '%c' (0x%02x)\n", ch, (unsigned char)ch);
                }

                // Create a minimal parsing context
                tinyobj::v3::ParserConfig config;
                tinyobj::v3::ObjParser parser(config);

                // We can't easily call parseFloat from here without ParseState
                // Let's just check what readWord gives us
                std::string value_str;
                if (tinyobj::v3::detail::readWord(line_reader, value_str)) {
                    printf("  Value string: '%s'\n", value_str.c_str());
                }
            }
        }
    }

    return 0;
}
