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

sig DateTime
{
	second: one Int,
	minute: one Int,
	hour: one Int,
	day: one Int,
	month: one Int,
	year: one Int
}
{
	
	( 0 <= second and second <= 59) and
	( 0 <= minute and minute <= 59) and
	( 0 <= hour and hour <= 23) and
	( 1 <= day) and
	( 1 <= month and month <= 12) and
	( ( ( month = 11 or month = 4 or month = 6 or moth = 9 ) implies day <= 30) and
		( ( month = 1 or month = 3 or month = 5 or moth = 7 or month = 8 or month = 10 or month = 12 ) implies day <= 31 ) and
		( (month = 2 and year % 4 != 0 ) implies day <= 28 ) and
		((month = 2 and year % 4 = 0) implies day <= 29) )
}

pred TimePrecedent [ dt1, dt2: DateTime]	// u1 succedes u2
{
	( u1.year > u2.year ) or
	( u1.year = u2.year and u1.month > u2.month ) or
	( u1.year = u2.year and u1.month = u2.month and u1.day > u2.day) or
	( u1.year = u2.year and u1.month = u2.month and u1.day = u2.day and u1.hour > u2.hour ) or
	( u1.year = u2.year and u1.month = u2.month and u1.day = u2.day and u1.hour = u2.hour and u1.minute > u2.minute ) or
	( u1.year = u2.year and u1.month = u2.month and u1.day = u2.day and u1.hour = u2.hour  and u1.minute = u2.minute and u1.second > u2.second ) 
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
