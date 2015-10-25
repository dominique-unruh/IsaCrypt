
import tests
import unittest

class wp(unittest.TestCase):
    def test_wp_more(self): tests.run_theory('tests/wp_more.thy')
    def test_wp_if(self): tests.run_theory('tests/wp_if.thy')
    def test_wp_assign(self): tests.run_theory('tests/wp_assign.thy')
    def test_wp_skip(self): tests.run_theory('tests/wp_skip.thy')

class dummy(unittest.TestCase):
    def test_fail(self): tests.run_theory('tests/fail.thy')
    def test_succeed(self): tests.run_theory('tests/succeed.thy')

class seq(unittest.TestCase):
    def test_seq(self): tests.run_theory('tests/seq.thy')

class utils(unittest.TestCase):
    def test_close_keyword(self): tests.run_theory('tests/close_keyword.thy')
    def test_close_keyword_fail2(self): tests.run_theory('tests/close_keyword_fail2.thy')
    def test_termx_antiquot(self): tests.run_theory('tests/termx_antiquot.thy')
    def test_close_keyword_fail(self): tests.run_theory('tests/close_keyword_fail.thy')

class inline(unittest.TestCase):
    def test_inline(self): tests.run_theory('tests/inline.thy')
    def test_inline_rename(self): tests.run_theory('tests/inline_rename.thy')

class procs(unittest.TestCase):
    def test_def_by_spec(self): tests.run_theory('tests/def_by_spec.thy')

if __name__ == "__main__":
    unittest.main()
