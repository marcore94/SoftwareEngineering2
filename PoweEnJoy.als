sig Position
{
	latitude: one Int,	//should be float
	longitude: one Int	//should be float
}

abstract sig User
{
	name: one string,
	surname: one string,
	email: one string,
	password: one string,
	licence: one string,
	actualPosition: one Position
}

fact emailIsUnique
{
	all u1,u2: User | (u1!=u2)=> u1.email != u2.email
}

sig Client extends User
{}

sig Operator extends User
{}

sig Car
{
	driver: lone User,
	actualPosition: one Position,
	code: one Int,
	batteryLevel: one Int
}
{
	batteryLevel >= 0 and batteryLevel <= 100
}

fact codesOfTheCarsAreUnique
{
	all c1, c2: Car | (c1!=c2)=>c1.code!=c2.code
}

sig SafeArea
{
	position: one Position
}

sig ChargingArea extends SafeArea
{
	numberOfPlugs: one Int,
	chargingCars: set Car
}
{
	numberOfPlugs > 0 and
	#chargingCars <= numberOfPlugs
}

sig Reservation
{
	client: one Client,
	reservedCar: one Car,
	time: one DateTime,
	expirationFee: lone Payment
}

sig Ride
{
	client: one Client,
	startTime: one DateTime,
	finishTime: one DateTime,
	reservation: one Reservation,
	passengers: one Int,
	payment: one Payment
}
{
	passengers >= 0 and passengers <= 4
}

sig Payment
{
	charge: one Int, //should be float
	client: one Client,
	dateTime: one DateTime
}

fact payOnlyReservationFeeOrRide
{
	no p: Payment | some re: Reservation, ri : Ride | re.payment = p and ri.reservation = re
}

fact userWhoReservesPays
{
	all ri:Ride | ri.payment.client = ri.client,
	all re:Reservation | re.expirationFee.client = re.client
}
