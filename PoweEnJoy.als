sig Position
{
	latitude: one float,
	longitude: one float
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

sig Client extends User
{}

sig Operator extends User
{}

sig Car
{
	driver: lone User,
	actualPosition: one Position,
	batteryLevel: one Int
}
{
	batteryLevel >= 0 and batteryLevel <= 100
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
	charge: one float,
	dateTime: one DateTime
}

fact payOnlyReservationFeeOrRide
{
	no p: Payment | some re: Reservation, ri : Ride | re.payment = p and ri.reservation = re
}
