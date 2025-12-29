import math
import random
random.seed(2025)

u_digits, v_digits = 2, 2
u_start, v_start = 10 ** (u_digits - 1), 10 ** (v_digits - 1)
u_end, v_end = u_start * 10, v_start * 10

good_threshold = .1 # relative to `min(u,v)`.
too_good_threshold = .3 # exclusive.
#good_threshold, too_good_threshold = .5, .99
limit = 100 # how many to print.
mode = 'random' # or 'exhaustive'.

print('u\tv\tgcd\tgoodness')
found = 0

def process(u, v):
	global found
	gcd = math.gcd(u, v)
	w = min(u, v)
	if good_threshold * w <= gcd < too_good_threshold * w:
		print(f'{u}\t{v}\t{gcd}\t{gcd / w}')
		found += 1

if mode == 'exhaustive':
	for u in range(u_start, u_end):
		for v in range(v_start, v_end):
			process(u, v)
			if found > limit:
				break
elif mode == 'random':
	while found < limit:
		u = random.randrange(u_start, u_end)
		v = random.randrange(v_start, v_end)
		process(u, v)