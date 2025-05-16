# # An x86-64 (Mac/Linux) JIT demo in Python
#
# **License:** MIT
# **Copyright:** (c) 2025 Dave Long
#
# In order to execute expressions parsed by Maxwell Bernstein's precedence
# climbing [parser](https://pdubroy.github.io/200andchange/precedence-climbing/), we use a rudimentary assembler to put together threaded
# opcode blocks in post-order, keeping our intermediates on the `rsp` stack.
#
# Obtaining an executable page and just-in-time loading the assembled code
# into it is accomplished via the help of `ctypes`, on SYSV ABI platforms.
# ------------------------------------------------------------------------------

from ctypes      import cast, CFUNCTYPE, POINTER, pythonapi
from ctypes      import c_char, c_int, c_long, c_char_p, c_void_p, c_size_t
from dataclasses import dataclass, field
from os          import name
from platform    import processor, machine
from sys         import maxsize
from typing      import List, Tuple

class JitError(Exception):
    pass

# ------------------------------------------------------------------------------

# `Asm` builds an assembled expression. Most opcodes are position-independent,
# and are kept in the `ops` array, but call offsets are `rip`-relative and
# hence vary at runtime, so we keep relocations in the `rels` array for them.
@dataclass
class Asm:
    ops: List[int]             = field(default_factory=list)
    rels: List[Tuple[int,int]] = field(default_factory=list)

    # `dot` returns the current offset relative to the start
    def dot(self) -> int:
        return len(self.ops)

    # `db` defines bytes, which we use to specify opcodes
    # in lieu of a more powerful assembler
    def db(self, v: List[int]):
        self.ops.extend(v)

    # `dd` defines a (little endian) dword
    def dd(self, v: int):
        self.db([(v>>8*i)&0xff for i in range(4)])

    # `dq` defines a (little endian) quadword
    def dq(self, v: int):
        self.db([(v>>8*i)&0xff for i in range(8)])

    # `reloc` defines a relocation entry specifying
    # opcode data which must be fixed up at load time
    def reloc(self, dst: int):
        self.rels.append((self.dot(), dst))
        self.dd(0)

# Assemble 0-address threaded code blocks for the various operations.
# (See also some of [dmr's threaded code](http://squoze.net/NB/nbilib.s))
def add(a):
    a.db([0x59,0x58,0x48,0x01,0xc8,0x50])

def sub(a):
    a.db([0x59,0x58,0x48,0x29,0xc8,0x50])

def mul(a):
    a.db([0x59,0x58,0x48,0xf7,0xe9,0x50])

def div(a):
    a.db([0x59,0x58,0x48,0x99,0x48,0xf7,0xf9,0x50])

def leq(a):
    a.db([0x59,0x58,0x48,0xff,0xc1,0x48,0x29,0xc8,0x48,0x99])
    a.db([0x48,0x83,0xe2,0x01,0x52])

def lt(a):
    a.db([0x59,0x58,0x48,0x29,0xc8,0x48,0x99,0x48,0x83,0xe2,0x01,0x52])

def neg(a):
    a.db([0x59,0x48,0x31,0xc0,0x48,0x29,0xc8,0x50])

# to handle `^` we call back into python code
@CFUNCTYPE(c_long, c_long,c_long)
def py_exp(a,b):
    return a**b if 0<=b else 0 # not quite right

def exp(a):
    a.db([0x5e,0x5f,0x53,0x48,0x89,0xe3,0x48,0x83,0xe3,0x08,0x48,0x29,0xdc])
    a.db([0xe8]); a.reloc(cast(py_exp,c_void_p).value)
    a.db([0x48,0x01,0xdc,0x5b,0x50])

# for simplicity `lit`eral data is always coded as a quad immediate
def lit(a,v):
    a.db([0x48,0xb8]); a.dq(v)
    a.db([0x50])

# given a concrete syntax tree, `codegen` assembles the threaded
# code blocks in order to calculate its value
def codegen(a:Asm, cst) -> Asm:
    gentab = {
    ('+',2): add, ('-',2): sub,
    ('*',2): mul, ('/',2): div,
    ('^',2): exp, ('negate',1): neg,
    ('<=',2): leq, ('<',2): lt,
    # allow ascii-syntax operations as well
    ('add',2): add, ('sub',2): sub,
    ('mul',2): mul, ('div',2): div,
    ('exp',2): exp,
    }
 
    # `gen` does a syntax-directed tree walk. Gen of
    # `['+',1,['*',2,3]]` assembles the concatenation `<1> <2> <3> * +`
    def gen(a:Asm, cst):
        if isinstance(cst,int):
            lit(a,cst)
        elif isinstance(cst,list):
            key = (cst[0],len(cst)-1)
            if key in gentab:
                # we process the syntax tree in postorder
                for arg in cst[1:]:
                  gen(a,arg)
                gentab[key](a)
            else:
                raise JitError("unimplemented func")
        else:
            raise JitError("unimplemented literal")
 
    gen(a, cst)
    a.db([0x58,0xc3])
    return a

# ------------------------------------------------------------------------------

Thunk = CFUNCTYPE(c_long)

# `JitPage` grubs around with `ctypes` to load and execute the assembled code.
# The address of our executable page is `adr` and it extends `len` bytes.
class JitPage:
    valid: bool
    adr: int
    len: int

    def __init__(self):
        # there *has* to be a better way to check for SYSV x86-64!?
        if name != 'posix' or maxsize != 2**63-1 or (not
           any("86" in f for f in [processor(),machine()])):
            self.len   = 0
            self.adr   = 0
            self.valid = False
        else:
            # establish some libc linkages
            mc  = pythonapi.memcpy
            mc.argtypes = (c_void_p,c_char_p,c_size_t)
            ms  = pythonapi.memset
            ms.argtypes = (c_void_p,c_char,c_size_t)
            mm  = pythonapi.mmap
            mm.restype = c_void_p
            mm.argtype = (c_void_p,c_size_t,c_int,c_int,c_int,c_size_t)
            # allocate RWX page
            self.len   = pythonapi.getpagesize()
            self.adr   = pythonapi.mmap(0, self.len, 7, 0x1022, -1, 0)
            self.valid = True

    # `fixup` is called if necessary at load time to encode `rip`-relative
    # offsets between our calls and their referents
    def fixup(self, off:int, dst:int):
        # assumption: our page and ctypes' thunks are within 32 bits
        adr = self.adr+off
        rel = dst - (adr+4)
        buf = cast(adr, POINTER(c_char*4)).contents
        buf[:] = [(rel>>8*i)&0xff for i in range(4)]

    # `load` copies assembled code into the RWX page,
    # returning a function pointer to the start of the assembly.
    def load(self, a:Asm) -> Thunk:
        if not self.valid:
            raise JitError("couldn't confirm posix x86-64")
        if a.dot() > self.len:
            raise JitError("too complex")
        # fill with breakpoints
        pythonapi.memset(self.adr, 0xcc, self.len)
        # load in the opcodes
        pythonapi.memcpy(self.adr, bytes(a.ops), a.dot())
        # fix up relative references
        for off,dst in a.rels:
            self.fixup(off,dst)
        return Thunk(self.adr)

    # `eval` assembles code for a parsed expression, loads, and executes
    def eval(self, expr) -> int:
        thunk = self.load(codegen(Asm(), expr))
        return thunk()

# ------------------------------------------------------------------------------

if __name__ == "__main__":
    j = JitPage()

    tests = [
    (0,0),
    (['negate',1],-1),
    (['*',3,['negate',2]],-6),
    (['^',3,2],9),
    (['+',1,['^',3,2]],10),
    (['/',['+',1,['-',['-',['*',4,10],['^',6,['+',1,1]]],['negate',1]]],2],3),
    (['+',['*',['<',1,1],1],['*',['<=',1,1],1]],1),
    (['+',['*',['<',1,4],1],['*',['<=',4,1],4]],1),
    (['+',['*',['<',1,4],4],['*',['<=',4,1],1]],4),
    (['+',['*',['<',4,4],4],['*',['<=',4,4],4]],4),
    (['add',1,['mul',2,3]],7),
    ]

    for xpr,res in tests:
        print(j.eval(xpr) == res)
 
    try:
        j.eval("1+"*500+"1")
        raise Exception
    except JitError:
        print(True)
