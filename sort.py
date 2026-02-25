import random

def randlist(N):
  res = []
  for i in range(N): res.append(random.randint(0,100))
  return res



l = randlist(20)

def check(l):
  for i in range(len(l)-1):
    if l[i] > l[i+1]: return False
  return True

print(l)

def swap(l, a, b):
  if b >= len(l):print(b)
  if b < 0: print(b)
  t = l[a]
  l[a] = l[b]
  l[b] = t


def inplacesort(l, start = 0 , end = None):
  print(start, end)
  if end == None: end = len(l)
  assert end <= len(l)

  if start >= end : return

  s = start
  e = end - 1

  tester = l[s]
  
  while s < e:
    while s < e and l[s] < tester:
      s += 1
    while s < e and l[e] > tester:
      e -= 1
    if s == e: break
    assert s < e
    swap(l, s, e)
    s += 1
    e -= 1
  
  for x in l[start:s]: assert x <= tester
  for (i, x) in enumerate(l[s:end]): assert x >= tester, f'{i,x, tester}: {start, s, e, end}'

  sort(l, start, s)
  sort(l, s, end)


def mergesort(l:list[int]) -> list[int]:
  if len(l) <= 1: return l
  s = len(l) // 2
  a, b = mergesort(l[:s]), mergesort(l[s:])
  res = []
  while True:
    if a == [] or b == []: return res + a + b
    if a[0] < b[0]: res.append(a.pop(0))
    else: res.append(b.pop(0))

def bubblesort(l:list[int]) -> list[int]:
  for i in range(len(l)):
    for j in range(i, len(l)):
      if (l[i] > l[j]): swap(l, i, j)
  return l

def paint(l):
  for x in l: print("+" * x)

paint(l)

print()
print()
print()
# paint(mergesort(l))
paint(bubblesort(l))

# print("sorted:")

# paint(l)

print(check(l))



