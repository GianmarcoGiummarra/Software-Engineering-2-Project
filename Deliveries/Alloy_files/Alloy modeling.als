module myTaxiService

//DATA TYPE

sig Text{}
sig Integer{}
sig Date{}
sig Time{}

//SIGNATURE

abstract sig User{
	name: lone Text,
	surname: lone Text,
	password: one Text
}

sig Customer extends User{
	email: one Text,
	dateOfBirth: one Date
}

sig TaxiDriver extends User{
	id: one Text,
	currentZone: one Integer,
	availableSeats: Integer
}

abstract sig Ride{
	id: one Text,
	carID: one Text,
	taxiDriver: one TaxiDriver,
	startingPosition: one Integer,
	startingTime: one Time,
	date: one Date,
	associatedCall: one Call
}

sig PrivateRide extends Ride{
	passenger: one Customer
}

sig SharedRide extends Ride{
	passengers: some Customer,
	steps: some Text
}

abstract sig Call{
	id: one Text,
	passenger: one Customer,
	queueStartingZone: one Integer,
	startingPosition: one Text,
	destinationPoint: one Text,
	date: one Date
}

sig ImmediateCall extends Call{}

sig ReservationCall extends Call{
	rideStartingTime: one Time
}

//ASSUMPTION

//Every user can not book more than one taxi in overlapping times.
assert noMoreThanOneTaxi{
	all r1,r2: Ride | (((r1.passenger = r2.passenger) or (r1.passenger in r2.passengers) or
							(r1.passengers & r2.passengers != none)) and r1.date = r2.date and
							r1.startingTime = r2.startingTime) implies r1 = r2
}

/*
	Every customer’s taxi request is processed by the system and forwarded to the first available taxi driver only in the queue
	of the same zone where the request comes from.
*/
fact taxiDriverCameFromTheCustomerZone{
	all c: Call, r: PrivateRide | (c.passenger = r.passenger) implies ( c.queueStartingZone = (r.taxiDriver).currentZone)
}

//Each cab belonging to the service is homologated with five seats, including the driver’s one.
fact maximumNumberOfAvailableSeats{
	#TaxiDriver.availableSeats >= 0
	#TaxiDriver.availableSeats <= 4
}

//Each registered user is related to one and only one e-mail address.
fact noDoubleUser{
	all c1, c2: Customer | c1.email = c2.email implies c1=c2
}

//Each customer is related to one and only one password.
fact onePasswordForEveryCustomer{
	all c1, c2: Customer | c1.password = c2.password implies c1 = c2
}

//Each taxi driver is related to one and only one taxi driver's ID.
fact noDoubleTaxiDriver{
	all t1,t2: TaxiDriver | t1.id = t2.id implies t1 = t2
}

//Each taxi driver related to one and only one password.
fact onePasswordForEveryTaxiDriver{
	all t1, t2: TaxiDriver | t1.password = t2.password implies t1 = t2
}

//Each call concerns one and only one ride.
fact noGhostCall{
	all r: Ride | # r.associatedCall <=1
}

//Each call concerns one and only one customer.
fact noGhostCustomer{
	all r: Ride | # r.passenger <=1
}

//The system can’t store the same ride in his memory twice.
fact noDoubleRide{
	no disj r1, r2 : Ride | r1.id = r2.id
}

//The system can’t store the same call in his memory twice.
fact noDoubleCall{
	no disj c1, c2 : Call | c1.id = c2.id
}

//A call and its associated ride must have the same date (the time can be different, e.g. for shared rides)
fact sameDateForCallAndAssociatedRide{
	all r: Ride, c: Call | r.associatedCall = c implies r.date = c.date
}

//In a private ride every car can carry one and only one customer
fact oneCarForEveryPrivateRideCustomer{
	all r: PrivateRide | #r.passenger = 1
}

pred show{}
run show
