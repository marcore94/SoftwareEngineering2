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
	actualPosition: one Position
	batteryLevel: one int
}
{
	batteryLevel >= 0 and batteryLevel <= 100,
}

sig SafeArea
{
	position: one Position
}

sig ChargingArea extends SafeArea
{
	numberOfPlugs: one int,
	chargingCars: set Car
}
{
	numberOfPlugs > 0,
	#chargingCars <= numberOfPlugs
}

sig Reservation
{
	client: one Client,
	reservedCar: one Car,
	time: one DateTime,
}

sig Ride
{
}
