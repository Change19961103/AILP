from caes import PropLiteral, Argument, ArgumentSet, ProofStandard, Audience, CAES
import sys
import os

# make Reader as one more file rather than write a new class in caes for making the code easy
# to read and easy to change

class Reader(object):

    def __init__(self):

        # construct appropriate lists or sets for every line which has correct grammar
        self.proof_standard = []
        self.main_query = []
        self.arg_if_then = {}
        self.default_standard = []
        self.comment = []
        self.arg_weights = {}
        self.assumptions = set()
        self.arg_result = {}
        self.current_arg = []
        self.arg_p = []
        self.arg_d = []
        self.acceptable = False
        self.accept = False
        self.current_cq = ''
        self.cq = []
        self.cq_already = []
        self.burden = 'Plaintiff'


    def seperate_data(self, data):
        """
        This function is to split the data to line in one array and check every line
        of the data whether its grammar is true, then add each line to its list
        :param text: input file
        :return: void
        """
        # split every line
        every_line = data.splitlines()
        every_line = self.delete_empty(every_line)
        for line in every_line:
            # print(line)
            # to delete the comment
            # check which part this line is belongs to
            if line[0] == '#' and line[1] == '#':
                self.comment.append(line)
            elif self.check_assumption(line):
                self.add_assumption(line)
            elif self.check_proof_standard(line):
                self.add_proof_standard(line)
            elif self.check_argument(line):
                self.add_arguments(line)

            elif self.check_main_query(line):
                self.add_main_query(line)
            elif self.check_default_standard(line):
                self.add_default_standard(line)
            else:
                raise TypeError('Your input line does not have a correct grammar')


    def seperate_Cq(self, data):
        every_line = data.splitlines()
        every_line = self.delete_empty(every_line)
        # print(every_line)
        for line in every_line:
            if self.check_cq(line):
                self.add_cq(line)


    def arg(self):
        """
        to build argset, proofstandard, argument and use the function in caes, adding them
        to graph
        :return: void
        """

        i = 0
        ps = self.proof_standard
        prop = PropLiteral(self.predicates(ps[0]))
        argset = ArgumentSet()

        # to confirm that user input a default proof standard, if not use 'scintilla'
        if len(self.default_standard) == 1:
            proofS = ProofStandard([(prop, ps[1])], default=self.default_standard[0])
        else:
            proofS = ProofStandard([(prop, ps[1])])

        # for key in self.arg_if_then:
        #     key_set.append(key)
        #     # take argument out from dictionary
        #     self.current_arg.append(self.arg_if_then[key])


        while i < len(self.current_arg):
            premises = set()
            exceptions = set()
            argument = self.seperate_arg(self.current_arg[i])
            # add the negate of this argument into ArgumentSet(), due to 'clear_and_convincing'
            pred = self.delete_not(self.predicates(argument[1]))
            argset.add_proposition(pred.negate())
            # first check unless inside
            if 'unless' in self.current_arg[i]:
                if 'and' in argument[0]:
                    # split from 'and'， 2 spaces before and after 'and', to prevent split words
                    # like 'band'
                    a = argument[0].split(' and ')
                    a = self.delete_space(a)
                    for element in a:
                        premises.add(self.delete_not(self.predicates(element)))
                        argset.add_proposition(self.delete_not(self.predicates(element)).negate())
                else:
                    premises.add(self.delete_not(self.predicates(argument[0])))
                    argset.add_proposition(self.delete_not(self.predicates(argument[0])).negate())
                if 'or' in self.current_arg[i]:
                    # 2 spaces before and after 'or', to prevent split words like boring
                    a = argument[2].split(' or ')
                    a = self.delete_space(a)
                    for element in a:
                        exceptions.add(self.delete_not(self.predicates(element)))
                        argset.add_proposition(self.delete_not(self.predicates(element)).negate())
                else:
                    exceptions.add(self.delete_not(self.predicates(argument[2])))
                    argset.add_proposition(self.delete_not(self.predicates(argument[2])).negate())
                argset.add_argument(Argument(self.delete_not(self.predicates(argument[1])), premises=premises,
                                             exceptions=exceptions), arg_id=self.find_argid(self.current_arg[i]))
            else:
                if 'and' in argument[0]:
                    a = argument[0].split(' and ')
                    a = self.delete_space(a)
                    for element in a:
                        premises.add(self.delete_not(self.predicates(element)))
                        argset.add_proposition(self.delete_not(self.predicates(element)).negate())
                else:
                    premises.add(self.delete_not(self.predicates(argument[0])))
                    argset.add_proposition(self.delete_not(self.predicates(argument[0])).negate())
                argset.add_argument(Argument(self.delete_not(self.predicates(argument[1])), premises=premises),
                                    arg_id=self.find_argid(self.current_arg[i]))
            i += 1

        argset.draw()
        argset.write_to_graphviz()

        # add negate of all assumption
        for element in self.assumptions:
            argset.add_proposition(element.negate())

        audience = Audience(self.assumptions, self.arg_weights)
        caes = CAES(argset, audience, proofS)

        # check whether user enters main query, if not notice user to enter main query
        if len(self.main_query) == 0:
            print('No main query include, please enter appropriate main query')
        else:
            return caes.acceptable(self.delete_not(self.predicates(self.main_query[0])))
            # caes.acceptable(self.delete_not(self.predicates(self.main_query[0])).negate())


    # search to get argid of argument
    def find_argid(self, arg):
        for (argid, result) in self.arg_if_then.items():
            if result == arg:
                return argid



    def bop_true(self):

        first = 1

        self.print_data()

        while len(self.current_arg) < len(self.arg_if_then):
            # assume always start with plaintiff
            exception = 0
            # print('-----------------------------')
            if first == 1:
                exception = 1
                # print('-----------------------')
                for (argid, result) in self.arg_result.items():
                    # print(result)
                    # print(self.main_query[0])
                    if self.main_query[0] == result:
                        self.current_arg.append(self.arg_if_then[argid])
                        self.arg_p.append((self.arg_if_then[argid]))
                        # print(self.arg_if_then[argid])
                        self.check_bop()
                        self.check_rec(self.arg_if_then[argid])
                        first = 0
            else:
                if self.burden == 'Defendant':
                    for arg in self.arg_p:
                        for (argid, result) in self.arg_result.items():
                            # print('not ' + result)
                            # print(self.predicates((self.seperate_arg(arg)[1])))
                            # to check the not argument to rebut other side
                            if result == ('not ' + self.predicates(self.seperate_arg(arg)[1])):
                                if self.arg_if_then[argid] not in self.current_arg:
                                    exception = 1
                                    if self.arg_if_then[argid] not in self.current_arg and self.arg_if_then[
                                        argid] not in self.arg_p:
                                        self.current_arg.append(self.arg_if_then[argid])
                                        self.arg_d.append((self.arg_if_then[argid]))
                                        self.check_bop()
                                        self.check_rec(self.arg_if_then[argid])

                else:
                    for arg in self.arg_d:
                        for (argid, result) in self.arg_result.items():
                            if result == ('not ' + self.predicates(self.seperate_arg(arg)[1])):
                                exception = 1
                                if self.arg_if_then[argid] not in self.current_arg and self.arg_if_then[
                                    argid] not in self.arg_p:
                                    self.current_arg.append(self.arg_if_then[argid])
                                    self.arg_p.append((self.arg_if_then[argid]))
                                    self.check_bop()
                                    self.check_rec(self.arg_if_then[argid])
            if exception == 0:
                break


    def match_cq(self, cq, arg):
        # if the predicate matches, then put the cq into list
        cq_list = []
        for args in arg:
            pred = args.split('(')[0]
            for cqs in cq:
                new_cqs = cqs.split(' ')
                # print(cqs)
                # print(pred)
                for word in new_cqs:
                    if pred == word:
                        cq_list.append([self.rep(cqs, args), args, cqs])
                        break
        return cq_list


    def rep(self, cq, arg):
        # replace the constant with variable
        cq_name = cq[1:]
        # print(cq_name)
        # print(cq)
        variable1 = ''
        variable2 = ''
        count = 1
        i = 0
        if ',' in arg:
            name = (arg.split('(')[1]).split(',')
            # print(name)
            while(i<len(cq_name)):
                if cq_name[i].isupper() and count == 2:
                    # print(name)
                    variable2 = cq[i+1]
                if cq_name[i].isupper() and count == 1:
                    # print(cq[i+1])
                    # print(name[0])
                    variable1 = cq[i+1]
                    count += 1
                i += 1

            cq = cq.replace(variable1, name[0])
            cq = cq.replace(variable2, name[1][:-1])
        elif '(' not in arg:
            return cq
        else:
            name = arg.split('(')[1]
            # print(name[:-1])
            while(i<len(cq_name)):
                if cq_name[i].isupper():
                    cq = cq.replace(cq[i+1],name[:-1])
                i += 1
        return cq


    def predicate_arg(self, arg):
        # change every premises exception result in argument to predicate form
        # print(arg)
        sep = self.seperate_arg(arg)
        # print(sep)
        new_list = []
        pre_arg = []
        predicate = []
        if len(sep) == 2:
            # print(sep[0])
            # print(sep[1])
            new_list += sep[0].split(' and ')
            new_list.append(sep[1])
            # print(new_list)
        else:
            new_list += sep[0].split(' and ')
            new_list.append(sep[1])
            new_list += sep[2].split(' or ')
        # print(new_list)
        for args in new_list:
            pre_arg.append(self.predicates(args))
        # print(pre_arg)
        return pre_arg


    def check_rec(self, arg):
        # print(self.predicate_arg(arg))
        cq_list = self.match_cq(self.cq, self.predicate_arg(arg))
        # print(cq_list)
        for cqs in cq_list:
            # print(cqs)
            if cqs[0] not in self.cq_already:
                self.current_cq = cqs[0]
                self.cq_already.append(cqs[0])
                # print(cqs[0])
                # print(self.cq)
                # print(cqs[2])
                # self.cq.remove(cqs[2])
                for (id, res) in self.arg_result.items():
                    # print(cqs[1])
                    # print(res)
                    if cqs[1] == res:
                        # print(self.arg_if_then[id])
                        if self.arg_if_then[id] not in self.current_arg and self.arg_if_then[id] not in self.arg_p:
                            self.current_arg.append(self.arg_if_then[id])
                            if self.burden == 'Plaintiff':
                                self.arg_p.append(self.arg_if_then[id])
                            else:
                                self.arg_d.append(self.arg_if_then[id])
                            self.check_bop()
                            self.check_rec(self.arg_if_then[id])
        arg = arg.split(' then ')
        arg = arg[0][3:]
        arg = arg.split(' and ')
        # print(arg)
        for (argid, result) in self.arg_result.items():
            for value in arg:
                if result == self.predicates(value):
                    # print(result)
                    if self.arg_if_then[argid] not in self.current_arg and self.arg_if_then[argid] not in self.arg_p:
                        self.current_arg.append(self.arg_if_then[argid])
                        if self.burden == 'Plaintiff':
                            self.arg_p.append(self.arg_if_then[argid])
                        else:
                            self.arg_d.append(self.arg_if_then[argid])
                        self.check_bop()
                        self.check_rec(self.arg_if_then[argid])


    def get_exception(self, arg):
        arg = arg.split(' unless ')[1]
        arg = arg.split(' or ')
        return arg




    def print_data(self):
        # output the data
        print('Current argument: ')
        for ca in self.current_arg:
            print(self.argument(ca))
        print('')
        print('Main query acceptable: {}'.format(self.acceptable))
        print('')
        print('Burden of proof: {}'.format(self.burden))
        print('')
        print('Current critical question: {}'.format(self.current_cq))
        print('---------------------------------------')
        self.current_cq = ''


    def argument(self, arg):
        # print(arg)
        premises = set()
        exceptions = set()
        new_list = self.seperate_arg(arg)
        if ' unless ' in arg:
            for element in new_list[0].split(' and '):
                premises.add(self.delete_not(self.predicates(element)))
            for element in new_list[2].split(' or '):
                exceptions.add(self.delete_not(self.predicates(element)))
            return Argument(self.delete_not(self.predicates(new_list[1])), premises=premises, exceptions=exceptions)
        else:
            for element in new_list[0].split(' and '):
                premises.add(self.delete_not(self.predicates(element)))
            return Argument(self.delete_not(self.predicates(new_list[1])), premises=premises)


    def check_bop(self):
        # check the acceptable of main query
        self.accept = self.arg()
        if self.accept != self.acceptable:
            self.acceptable = self.accept
            if self.burden == 'Plaintiff':
                self.burden = 'Defendant'
            else:
                self.burden = 'Plaintiff'
        self.print_data()


    def check_cq(self, line):
        check_list = line.split('cq:')
        check_list = self.delete_empty(check_list)
        if len(check_list) == 1 and check_list[0] != line :
            return True
        else:
            return False


    def add_cq(self, line):
        line = line.split('cq: ')[1]
        self.cq.append(line)


    def seperate_arg(self, arg):
        """
        seperate the argument to 3 parts(if has unless) or 2 parts
        :param arg: input argument
        :return: list
        """
        arg_content1 = []
        arg_content2 = []
        # first check wheter unless is inside or not
        # if unless is in the argument, then seperates argument to 3 parts
        if 'unless' in arg:
            three_parts = arg.split('If ')
            for element in three_parts:
                arg_content1 += element.split(' then ')
            for element in arg_content1:
                arg_content2 += element.split(' unless ')
            arg_content2 = self.delete_empty(arg_content2)
            arg_content2 = self.delete_space(arg_content2)
            return arg_content2
        else:
            three_parts = arg.split('If ')
            for element in three_parts:
                arg_content1 += element.split(' then ')
            arg_content1 = self.delete_empty(arg_content1)
            arg_content1 = self.delete_space(arg_content1)
            return arg_content1


    def check_argument(self, line):
        """
        This function is to check whether input line belongs to argument
        :param line: input line
        :return: boolean
        """
        list_argument = []
        # get the colon index then check number
        index_colon = [index for (index, colon) in enumerate(line) if colon == ':']
        if len(index_colon) == 2 and index_colon[1] - index_colon[0] != 1:
            arg = line.split(':')
            arg = self.delete_space(arg)
            has_if = 'If ' in arg[1]
            has_then = ' then ' in arg[1]
            # argName is not empty
            if arg[0] == '':
                return False
            # check the last part is weight
            if not self.check_weight(arg[2]):
                return False
            # argument has if then structure
            if has_then and has_if:
                argument = arg[1].split('If ')
                argument = self.delete_space(argument)
                for element in argument:
                    list_argument = list_argument + (element.split(' then '))
                    list_argument = self.delete_space(list_argument)
                list_argument = self.delete_empty(list_argument)
                # there are words after if and after then
                if len(list_argument) == 2:
                    return True
        else:
            return False



    def check_proof_standard(self, line):
        """
        this function is to check whether input line belongs to proof standard
        :param line: input line
        :return: boolean
        """
        check_list = line.split('Proof standard:')
        check_list = self.delete_empty(check_list)
        # split from proof standard if it has proof standard and there are words after proof standard
        # the length of list will be 1
        if len(check_list) == 1 and check_list[0] != line :
            content = check_list[0].split(':')
            content = self.delete_space(content)
            content = self.delete_empty(content)
            if len(content) == 2:
                return True
        else:
            return False


    def check_assumption(self, line):
        """
        this function is to check whether input line belongs to assumption
        :param line: input line
        :return: boolean
            """
        # split by assumption
        check_list = line.split('Assumption:')
        check_list = self.delete_empty(check_list)
        # check whether there are words after assumption and if
        # there is no assumption in this line, after split, line
        # will not change
        if len(check_list) == 1 and check_list[0] != line :
            return True
        else:
            return False


    def check_main_query(self, line):
        """
         this function is to check whether input line belongs to main query
        :param line: input line
        :return: boolean
        """
        # almost the same mean as assumption
        check_list = line.split('Main query:')
        check_list = self.delete_empty(check_list)
        if check_list[0] != line:
            return True
        else:
            return False


    def check_default_standard(self, line):
        """
        this function is to check whether input line belongs to default proof standard
        :param line: input line
        :return: boolean
        """
        check_list = line.split('Default proof standard:')
        check_list = self.delete_empty(check_list)
        check_list = self.delete_space(check_list)
        if len(check_list) == 1 and check_list[0] != line :
            return True
        else:
            return False


    def check_weight(self, element):
        """
        to check whether the input element is weight in range 0 to 1
        :param element: the input string
        :return: boolean
        """
        # whether the number is from 0.0 to 1.0
        if float(element) >=0 and float(element) <= 1:
            return True
        else:
            raise ValueError('weights is a number between 0 and 1')


    def add_arguments(self, line):
        """
        add this line which is argument to the dictionary of argument
        :param line: input line
        :return: void
        """
        three_parts = line.split(':')
        three_parts = self.delete_space(three_parts)
        three_parts = self.delete_empty(three_parts)
        self.arg_if_then[three_parts[0]] = three_parts[1]
        self.arg_weights[three_parts[0]] = float(three_parts[2])
        self.arg_result[three_parts[0]] = self.predicates(self.seperate_arg((three_parts[1]))[1])




    def add_proof_standard(self, line):
        """
        add this line which is proof standard to the list of proof standard
        :param line: input line
        :return: void
        """
        two_parts = line.split('Proof standard:')
        two_parts = self.delete_empty(two_parts)
        a = self.delete_space(two_parts[0].split(':'))
        a[0] = self.predicates(a[0])
        self.proof_standard += a

    def add_assumption(self, line):
        """
        add this line which is assumption to the list of assumption
        :param line: input line
        :return: void
        """
        one_part = line.split('Assumption:')
        one_part = self.delete_space(one_part)
        one_part = self.delete_empty(one_part)
        self.assumptions.add(self.delete_not(self.predicates(one_part[0])))


    def add_main_query(self, line):
        """
        add this line which is main_query to the list of main_query
        :param line: input line
        :return: void
        """
        one_part = line.split('Main query:')
        one_part = self.delete_space(one_part)
        one_part = self.delete_empty(one_part)
        self.main_query.append(self.predicates(one_part[0]))


    def add_default_standard(self, line):
        """
        add this line which is default proof standard to the list of default proof standard
        :param line: input line
        :return: void
        """
        one_part = line.split('Default proof standard:')
        one_part = self.delete_space(one_part)
        one_part = self.delete_empty((one_part))
        self.default_standard += one_part


    def delete_space(self, list):
        """
        this function will delete all the space at the begin or at the end of a string
        for every element in a list
        :param list: a input list
        :return: list
        """
        list_nospace = []
        for element in list:
            list_nospace.append(element.strip())
        return list_nospace


    def delete_empty(self, list):
        """
        delete all the '' in a list
        :param list: input list
        :return: list
        """
        list_noempty = []
        for element in list:
            if element != '':
                list_noempty.append(element)
        return list_noempty


    def delete_not(self, str):
        """
        delete all the not, if str has odd number of not, change its polarity
        :param str: a input str
        :return: PropLiteral of this str
        """
        not_count = 0
        while str[:4] == 'not ':
            str = str[4:].strip()
            not_count += 1
        if not_count % 2 == 0:
            return PropLiteral(str)
        else:
            return PropLiteral(str).negate()


    def predicates(self, str):
        """
        this function can change the string in propliteral to from name pred name to pred(name, name)
        or pred name to pred(name)
        :return: void
        """
        # check the position of '"'
        index_quota = [index for (index, quota) in enumerate(str) if quota == '"']
        # check there is 1 constant in the str
        if self.has_constant(str) == 2:
            # check '"' inside
            constant = str[index_quota[0]+1:(index_quota[1])]
            # check constant is in the front or at the last
            if len(str) - index_quota[1] < index_quota[0]:
                name_pred = str[0:index_quota[0]].strip()
                name_pred = name_pred.split(' ')
                name_pred = self.delete_space(self.delete_empty(name_pred))
                return name_pred[1] + '(' + name_pred[0] + ',' + '"' +constant + '"' + ')'
            else:
                name_pred = str[(index_quota[1]+1):len(str)].strip()
                name_pred = name_pred.split(' ')
                name_pred = self.delete_space(self.delete_empty(name_pred))
                return name_pred[0] + '(' + name_pred[1] + ',' + '"' + constant + '"' + ')'
        # check there are 2 constant in the str
        elif self.has_constant(str) == 4:
            constant1 = str[index_quota[0]+1:index_quota[1]].strip()
            constant2 = str[(index_quota[2]+1):index_quota[3]].strip()
            pred = str[index_quota[1]+1 : index_quota[2]]
            return pred + '(' + '"' + constant1 + '"' + ',' + constant2 + ')'

        else:
            return self.change_pred(str)



    def change_pred(self, str):
        prop = self.delete_count_not(str)
        # print(prop)
        prop[0] = prop[0].strip()
        prop_new = self.delete_empty(prop[0].split(' '))

        # check unary or binary
        if prop[1] % 2 == 0:
            if len(prop_new) == 2:
                return prop_new[0] + '(' + prop_new[1] + ')'
            elif len(prop_new) == 3:
                return prop_new[1] + '(' + prop_new[0] + ',' + prop_new[2] + ')'
            else:
                return prop_new[0]
        else:
            if len(prop_new) == 2:
                return 'not ' + prop_new[0] + '(' + prop_new[1] + ')'
            elif len(prop_new) == 3:
                return 'not ' + prop_new[1] + '(' + prop_new[0] + ',' + prop_new[2] + ')'
            else:
                return 'not ' + prop_new[0]


    def has_constant(self, str):
        """
        to check whether this string has constant
        :return:
        """
        index_quota1 = [index for (index, quota) in enumerate(str) if quota == '"']
        if len(index_quota1) == 2 and index_quota1[1] - index_quota1[0] != 1:
            return 2
        elif len(index_quota1) == 4 and index_quota1[1] - index_quota1[0] != 1 and index_quota1[3] - index_quota1[2] != 1:
            return 4
        else:
            return 0


    def delete_count_not(self, str):
        not_count = 0
        while str[:4] == 'not ':
            str = str[4:].strip()
            not_count += 1
        return [str, not_count]




if __name__ == '__main__':
        reader = Reader()
        # print(sys.argv)
        data_open = open(sys.argv[1], 'r')
        data = data_open.read()
        cqs = os.path.abspath(os.path.dirname(__file__)) + "/cq.txt"
        cq = open(cqs, 'r')
        question = cq.read()
        reader.seperate_data(data)
        # print('the main query is {}'.format(reader.main_query))
        # print('the arg_if_then is {}'.format(reader.arg_if_then))
        # print('the assumption is {}'.format(reader.assumptions))
        # print('the arg_result is {}'.format(reader.arg_result))
        # reader.arg()
        reader.seperate_Cq(question)
        # print(reader.cq)
        reader.bop_true()
        # print(reader.current_arg)
