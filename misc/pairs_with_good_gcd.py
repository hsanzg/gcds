import math

u_start, u_end, v_start, v_end = 50000, 70000, 18000, 30000
u_start, u_end, v_start, v_end = 5000, 5100, 8000, 9000
u_start, u_end, v_start, v_end = 28, 40, 65, 75
#u_start, u_end, v_start, v_end = 110, 130, 550, 555
good_threshold = .002 # relative to `min(u,v)`.
too_good_threshold = .08 # exclusive.
good_threshold, too_good_threshold = .1, .499
limit = 100 # how many to print.

print('u\tv\tgcd\tgoodness')
found = 0
for u in range(u_start, u_end):
	for v in range(v_start, v_end):
		gcd = math.gcd(u, v)
		w = min(u, v)
		if good_threshold * w <= gcd < too_good_threshold * w:
			print(f'{u}\t{v}\t{gcd}\t{gcd / w}')
			found += 1
			if found > limit:
				break