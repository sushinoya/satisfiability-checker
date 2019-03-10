test_file = "uf20-01.cnf"
test, lines = [], [line.rstrip('\n') for line in open(test_file) if line[0] not in 'pc%0']
for line in lines:
  word_vars = [('a' + str(a) if int(a) > 0 else 'not({})'.format('a' + str(abs(int(a))))) for a in line.split()]
  clause = '[{}]'.format(', '.join(word_vars))
  if '[]' not in clause: test.append(clause)

print("dp([{}]).".format(', '.join(test)))