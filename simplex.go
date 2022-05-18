package lp

import (
	"fmt"
	"math"
)

const (
	EPS = 1.0e-6
)

func simplex(a [][]float64, n, m1, m2, m3 int64) (icase int64, izrov, iposv []int64, err error) {
	m := m1 + m2 + m3
	if int64(len(a)) != m+3 {
		err = fmt.Errorf("Bad input, a must have %d rows", m+3)
		return
	}
	izrov = make([]int64, n+1)
	iposv = make([]int64, m+1)
	l1 := make([]int64, n+1)
	l2 := make([]int64, m+1)
	l3 := make([]int64, m+1)
	nl1 := n                         // initially make all variables right-hand
	for k := int64(1); k <= n; k++ { // initialize index lists
		l1[k] = k
		izrov[k] = k
	}
	nl2 := m                         // make all artificial variables left hand
	for i := int64(1); i <= m; i++ { // initialize those lists.
		if int64(len(a[i])) != n+2 { // verify the length of the rows.
			err = fmt.Errorf("Bad input, each row of a must have length == %d, row %d has len = %d", n+2, i, len(a[i]))
			return
		}
		if a[i+1][1] < 0 { // bn must be non-negative
			err = fmt.Errorf("Bad input, b%d must be >= 0", i)
			return
		}
		l2[i] = i
		iposv[i] = n + i
	}
	for i := int64(1); i <= m2; i++ {
		l3[i] = i
	}
	phase1 := false // This flag setting means we are in phase one, ie have a feasible starting solution. Assume we can go to phase 2

	// Go to phase two if origin is a feasible solution
	if m2+m3 > 0 {
		phase1 = true // stay in phase1
		var kp int64
		var bmax float64
		for k := int64(1); k <= n+1; k++ { // compute auxiliary objective function
			q1 := float64(0)
			for i := int64(m1 + 1); i <= m; i++ {
				q1 += a[i+1][k]
			}
			a[m+2][k] = -q1
		}
		for phase1 {
			kp, bmax = simp1(a, m+1, nl1, l1, false) // find max coefficient of auxiliary objective function
			if bmax <= EPS && a[m+2][1] < -EPS {
				icase = -1 // Auxiliary objective function is still negative and cannot be improved, no feasible solution exists
				return
			}
			var ip int64
			skipSimp2 := false
			if bmax <= EPS && a[m+2][1] <= EPS { // if auxiliary objective function is 0 and cannot be improved.
				m12 := m1 + m2 + 1
				if m12 <= m { // this signals that we have a feasible starting vector
					for ip = m12; ip <= m; ip++ { // clean out the artificial variables
						if iposv[ip] == ip+n {
							kp, bmax = simp1(a, ip, nl1, l1, true)
							if bmax > 0 {
								skipSimp2 = true
								break
							}
						}
					}
				}
				if !skipSimp2 {
					phase1 = false // indicate we can move to phase 2
					m12 -= 1
					if m1+1 <= m12 {
						for i := m1 + 1; i <= m12; i++ {
							if l3[i-m1] == 1 {
								for k := int64(1); k <= n+1; k++ {
									a[i+1][k] *= -1
								}
							}
						}
					}
					break
				}
			}
			if !skipSimp2 {
				ip = simp2(a, n, l2, nl2, kp)
				if ip == 0 {
					icase = -1
					return
				}
			}
			simp3(a, m+1, n, ip, kp)
			if iposv[ip] >= n+m1+m2+1 {
				var k int64
				for k = 1; k <= nl1; k++ {
					if l1[k] == kp {
						break
					}
				}
				nl1 -= 1
				for is := k; is <= nl1; is++ {
					l1[is] = l1[is+1]
				}
				a[m+2][kp+1] += 1.0
				for i := int64(1); i <= m+2; i++ {
					a[i][kp+1] = -a[i][kp+1]
				}
			} else if iposv[ip] >= n+m1+1 {
				kh := iposv[ip] - m1 - n
				if l3[kh] != 0 {
					l3[kh] = 0
					a[m+2][kp+1] += 1.0
					for i := int64(1); i <= m+2; i++ {
						a[i][kp+1] = -a[i][kp+1]
					}
				}
			}
			is := izrov[kp]
			izrov[kp] = iposv[ip]
			iposv[ip] = is
		}
	}
	for {
		kp, bmax := simp1(a, 0, nl1, l1, false)
		if bmax <= 0 {
			icase = 0
			return
		}
		ip := simp2(a, n, l2, nl2, kp)
		if ip == 0 {
			icase = 1
			return
		}
		simp3(a, m, n, ip, kp)
		is := izrov[kp]
		izrov[kp] = iposv[ip]
		iposv[ip] = is
	}
	return
}

func simp1(a [][]float64, mm, nl1 int64, ll []int64, iabf bool) (kp int64, bmax float64) {
	kp = ll[1]
	bmax = a[mm+1][kp+1]
	for k := int64(2); k <= nl1; k++ {
		var test float64
		if iabf {
			test = math.Abs(a[mm+1][ll[k]+1]) - math.Abs(bmax)
		} else {
			test = a[mm+1][ll[k]+1] - bmax
		}
		if test > 0 {
			bmax = a[mm+1][ll[k]+1]
			kp = ll[k]
		}
	}
	return
}

func simp2(a [][]float64, n int64, l2 []int64, nl2, kp int64) (ip int64) {
	ip = 0
	for i := int64(1); i < nl2; i++ {
		if a[l2[i]+1][kp+1] < -EPS {
			q1 := -a[l2[i]+1][1] / a[l2[i]+1][kp+1]
			ip = l2[i]
			for i++; i <= nl2; i++ {
				ii := l2[i]
				if a[ii+1][kp+1] < -EPS {
					q := -a[ii+1][1] / a[ii+1][kp+1]
					if q < q1 {
						ip = ii
						q1 = q
					} else if q == q1 {
						var qp, q0 float64
						for k := int64(1); k <= n; k++ {
							qp = -a[ip+1][k+1] / a[ip+1][kp+1]
							q0 = -a[ii+1][k+1] / a[ii+1][kp+1]
							if q0 != qp {
								break
							}
						}
						if q0 < qp {
							ip = ii
						}
					}
				}
			}
		}
	}
	return
}

func simp3(a [][]float64, i1, k1, ip, kp int64) {
	piv := 1.0 / a[ip+1][kp+1]
	for ii := int64(1); ii < i1+1; ii++ {
		if ii-1 != ip {
			a[ii][kp+1] *= piv
			for kk := int64(1); kk <= k1+1; kk++ {
				if kk-1 != ip {
					a[ii][kk] -= a[ip+1][kk] * a[ii][kp+1]
				}
			}
		}
	}
	for kk := int64(1); kk <= k1+1; kk++ {
		if kk-1 != kp {
			a[ip+1][kk] *= -piv
		}
	}
	a[ip+1][kp+1] = piv
}
