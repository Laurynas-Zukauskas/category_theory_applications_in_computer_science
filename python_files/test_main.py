from quicksort import *
from sort_test import *

start = [4, 29, 28, 37, 8, 2]
start2 = p2i(start)
sorted_ind = quicksort(start2)
sorted = i2p(sorted_ind)
print(start)
print(sorted)