import struct

MASK = 0xFFFFFFFFFFFFFFFF

def xorshift64(state0, state1):
    s1 = state0
    s0 = state1
    state0 = state1
    s1 ^= (s1 << 23) & MASK
    s1 ^= (s1 >> 17) & MASK
    s1 ^= s0 & MASK
    s1 ^= (s0 >> 26) & MASK
    state1 = s1
    return state0, state1, None

def to_double(state0: int):
    u_long_long_64 = (state0 >> 12) | 0x3FF0000000000000
    float_64 = struct.pack("<Q", u_long_long_64)
    next_sequence = struct.unpack("d", float_64)[0]
    return next_sequence - 1  # Maps [1,2) to [0,1)

state1, state0 = (13688469645201006814, 217078821950813477)

for _ in range(3):
    state0, state1, generated = xorshift64(state0, state1)
    print((state0), (state1), to_double(state0))