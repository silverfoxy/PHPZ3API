import sys 

def get_api_interfaces(file_path):
    API_functions = []
    with open(file_path) as f:
        Function_lines = ''
        for line in f:
            if len(line.strip()) > 1 and line[0] != '#':
                if 'Z3_API' in line and Function_lines == '':
                    if line.strip()[-1] == ';':
                        API_functions.append(line)
                        Function_lines = ''
                    else:
                        Function_lines += line
                elif Function_lines != '':
                    Function_lines += line
                    if line.strip()[-1] == ';':
                        API_functions.append(Function_lines)
                        Function_lines = ''
    for item in API_functions:
        print(item.rstrip().replace('Z3_API ', '').replace('(void)', '()'))

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Run: python ' + sys.argv[0] + ' /Path/to/z3_api.h')
        sys.exit(0)
    else:
        get_api_interfaces(sys.argv[1])