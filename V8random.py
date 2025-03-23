import struct
import z3


# Function copppied from https://github.com/PwnFunction/v8-randomness-predictor/blob/main/main.py
# I have no idea how it works
def getStates(sequence) -> tuple[int, int]:
    sequence = sequence[::-1]
    solver = z3.Solver()
    se_state0, se_state1 = z3.BitVecs("se_state0 se_state1", 64)
    for i in range(len(sequence)):
        se_s1 = se_state0
        se_s0 = se_state1
        se_state0 = se_s0
        se_s1 ^= se_s1 << 23
        # Logical shift instead of Arthmetric shift
        se_s1 ^= z3.LShR(se_s1, 17)
        se_s1 ^= se_s0
        se_s1 ^= z3.LShR(se_s0, 26)
        se_state1 = se_s1
        float_64 = struct.pack("d", sequence[i] + 1)
        u_long_long_64 = struct.unpack("<Q", float_64)[0]
        mantissa = u_long_long_64 & ((1 << 52) - 1)
        solver.add(int(mantissa) == z3.LShR(se_state0, 12))
    if solver.check() == z3.sat:
        model = solver.model()
        states = {}
        for state in model.decls():
            states[state.__str__()] = model[state]
        state0 = states["se_state0"].as_long()
        state1 = states["se_state1"].as_long()

        return state0, state1
    raise RuntimeError("No solution found")


# Python rewrite of https://github.com/v8/v8/blob/3bfafd1f08b18ebb10cebc3ae59402f50df93d06/src/base/utils/random-number-generator.h#L121
def xorshift64(state0, state1) -> tuple[int, int]:
    MASK = 0xFFFFFFFFFFFFFFFF

    s1 = state0
    s0 = state1
    state0 = state1
    s1 ^= (s1 << 23) & MASK
    s1 ^= (s1 >> 17) & MASK
    s1 ^= s0 & MASK
    s1 ^= (s0 >> 26) & MASK
    state1 = s1
    return state0, state1


# Python rewrite of https://github.com/v8/v8/blob/3bfafd1f08b18ebb10cebc3ae59402f50df93d06/src/base/utils/random-number-generator.h#L111
def to_double(state0: int) -> float:
    u_long_long_64 = (state0 >> 12) | 0x3FF0000000000000
    float_64 = struct.pack("<Q", u_long_long_64)
    next_sequence = struct.unpack("d", float_64)[0]
    return next_sequence - 1  # Maps [1,2) to [0,1)


# generator, that returns next random numbers
def solve(sequence):
    if len(sequence) != 64: print("Warning: sequence len is not 64. Errors might occur")
    # use z3 to calculate internal states
    state0, state1 = getStates(sequence[0:5])

    # save current states for later
    states = (state0, state1)

    index = 0
    num = None
    # run until array wraps
    while (to_double(state0) not in sequence) or index <= 5:
        index += 1
        state0, state1 = xorshift64(state0, state1)
        if index > len(sequence) + 64:
            # if sequence is to short raise error
            if len(sequence) != 64:
                raise RuntimeError("Sequence len to short. No results found")
            # if sequence len is equal to cache size pass
            state0, state1 = states
            num = 5
            break

        # [..............][..............][..............][..............]
        #         [..............................]
        #      54    10  !               ^
    if num is None:
        # find index where buffer edge is
        while to_double(state1) in sequence:
            state0, state1 = xorshift64(state0, state1)

        # calculate amount needed to get to the start of the buffer
        # addding 5 is because of getting first 5 elements to calculate state
        # padding = max(len(sequence) - (sequence.index(to_double(state0)) % 64) - index, 0) // 64 * 64
        padding = max(len(sequence) - index, 0) // 64 * 64
        num = (64 - sequence.index(to_double(state0)) + 5)
        num += padding
        # reset states
        state0, state1 = states

    # finally get to the start of the buffer
    for _ in range(num):
        state0, state1 = xorshift64(state0, state1)

    def refillCache():
        nonlocal state0
        nonlocal state1
        nonlocal cache

        cache = []
        for _ in range(64):
            state0, state1 = xorshift64(state0, state1)
            cache.append(to_double(state0))

    # prefill cache
    cache = []
    # calculate cache index, make sure it is in range
    cacheIndex = (5 - 1 - len(sequence) - num) % 64
    refillCache()

    while True:
        if cacheIndex < 0:
            refillCache()
            cacheIndex = 63
        # walk through cache in reverse order
        yield cache[cacheIndex]
        cacheIndex -= 1
