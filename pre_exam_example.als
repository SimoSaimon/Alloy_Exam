enum Bool {True, False}
// signatures
abstract sig trafficElement{}

sig Car {
	var loc: one trafficElement // location
}

sig Crossroad extends trafficElement {
	var acc: one Bool
}

sig Road extends trafficElement {
  from: one Crossroad,
  to: one Crossroad
}

// Constrains
fact {
	all r: Road | r.from != r.to
}

fact {
	always ( 
		all c: Car | stutter[c] or 
		(some i: Crossroad | moveToCrossroad[c, i]) or 
		(some r: Road | moveToRoad[c,r])
	)
}

// Modelling move
pred stutter [c: Car] {
	c.loc' = c.loc
}

pred moveToCrossroad[c: Car, i: Crossroad] {
	i in c.loc.to
	i.acc = False
	c.loc' = i
}

pred moveToRoad[c: Car, r: Road] {
	c.loc in r.from
	c.loc.acc = False
	c.loc' = r
}

pred p1 {
	world
	some disj r1,r2: Road | some c1, c2: Crossroad | r1.from = c1 and r2.to = c1 and r1.to = c2 and r2.from = c2
	some r1: Road | some c1, c2: Crossroad | r1.from = c1 and r1.to = c2 and (all r2: Road | r2.from != c2 or r2.to != c1)
}

pred p2 {
	world
	some c1, c2, c3: Car | not (c1.loc = c2.loc or c1.loc = c3.loc or c2.loc = c3.loc ) and
	after after after after after (c1.loc = c2.loc and c2.loc = c3.loc and c1.loc in Crossroad) and 
	(c1.loc' != c1.loc and c1.loc'' != c1.loc' and c1.loc''' != c1.loc'')
}

fun from2: Crossroad -> Road {
	{
		c1: Crossroad, r1: Road | c1 in r1.from
	}
}

// Initialize
assert try {
	always (
		all c: Car | all i: Crossroad | i in c.loc.to and i.acc = True implies c.loc' = c.loc
	)
}
pred world{
	#Car = 3
	Crossroad.acc = False
	#Crossroad = 3
	#Road = 4
}
run p2 for 10
check try
//run world for 10
