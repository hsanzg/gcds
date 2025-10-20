import math
import random
random.seed(2025)

u_start, u_end, v_start, v_end = 50000, 70000, 18000, 30000
u_start, u_end, v_start, v_end = 5000, 5100, 8000, 9000
u_start, u_end, v_start, v_end = 28, 40, 65, 75
u_start, u_end, v_start, v_end = 300, 310, 5000, 5100
u_start, u_end, v_start, v_end = 7600, 7700, 3400, 3490
u_start, u_end, v_start, v_end = 30000, 35000, 18000, 30000
#u_start, u_end, v_start, v_end = 110, 130, 550, 555

u_digits, v_digits = 4, 4
u_start, v_start = 10 ** u_digits, 10 ** v_digits
u_end, v_end = u_start * 10, v_start * 10

good_threshold = .001 # relative to `min(u,v)`.
too_good_threshold = .08 # exclusive.
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