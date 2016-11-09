sig Position
{
	latitude: one Int,	//should be float
	longitude: one Int	//should be float
}

fact noSameCoordinatesPositions
{
	all disjoint p1, p2: Position | p1.latitude != p2.latitude and p1.longitude != p2.longitude
}

pred InsideArea [car: Car, safeArea: SafeArea]
{
	car.actualPosition in safeArea.positions
}

sig UnregisteredUser
{}

abstract sig User
{
	/*name: one String,
	surname: one String,
	email: one String,
	password: one String,
	licence: one String,*/
	actualPosition: one Position
}

fact noUserInSamePosition
{
	all disjoint u1, u2: User | u1.actualPosition != u2.actualPosition
}

/*fact emailIsUnique
{
	all u1,u2: User | (u1!=u2)=> u1.email != u2.email
}*/

sig Client extends User
{}

sig Operator extends User
{}

sig Car
{
	driver: lone User,
	actualPosition: one Position,
	code: one Int,
	batteryLevel: one Int,
	state: one CarState
}
{
	batteryLevel >= 0 and batteryLevel <= 100
}

fact atMostOneCarForDriver
{
	all disjoint c1, c2 : Car | ( c1.driver != none and c2.driver != none ) implies c1.driver != c2.driver
}

fact noCarsInSamePosition
{
	all disjoint c1, c2: Car | c1.actualPosition != c2.actualPosition
}

abstract sig CarState {}

one sig Free extends CarState {}

one sig Charging extends Free {}

one sig Reserved extends CarState {}

one sig InUse extends CarState {}

fact noUserWhileChargingFreeOrReserved
{
	all c: Car | (c.state = Free or c.state = Reserved) implies c.driver = none
}

fact driverInsideWhileDriving
{
	all c: Car | c.state = InUse implies ( c.driver != none and c.actualPosition = c.driver.actualPosition )
}

fact codesOfTheCarsAreUnique
{
	all c1, c2: Car | (c1!=c2)=>c1.code!=c2.code
}

fact carStateInSafeArea
{
	all car: Car | (car.state = Free or car.state = Reserved) implies some safeArea: SafeArea | InsideArea[car, safeArea]
}

fact noEnergyLawViolation
{
	all car: Car | car.batteryLevel = 0 implies (car.state != InUse and car.state != Reserved)
}

sig SafeArea
{
	positions: set Position
}
{
	#positions > 0
}

fact noSharedPositions
{
	all disjoint sa1, sa2: SafeArea | sa1.positions & sa2.positions = none
}

sig ChargingArea extends SafeArea
{
	numberOfPlugs: one Int,
	chargingCars: set Car
}
{
	numberOfPlugs > 0 and
	numberOfPlugs <= #positions and
	#chargingCars <= numberOfPlugs
}

fact chargingCarsAreInTheChargingArea
{
	all car : Car, chargingArea : ChargingArea | car in chargingArea.chargingCars implies InsideArea [car, chargingArea]
}

fact chargingCarsAreInChargingStatus
{
	all c : Car | some ca: ChargingArea |( c in ca.chargingCars ) iff c.state = Charging 
}

pred addChargingCar (car, car' :Car, area, area': ChargingArea)
{
	car.code = car'.code and car.state != Charging and area.positions = area'.positions and
	car'.state=Charging and	area'.chargingCars = area.chargingCars + car' and InsideArea[car', area'] and InsideArea[car, area]
}

sig Reservation
{
	client: one Client,
	reservedCar: one Car,
	time: one DateTime,
	expirationFee: lone Payment
}

fact reservationExpiresOrThereIsRide
{
	all re:Reservation, ri1 : Ride | one ri2:Ride | 
	( ri1.reservation = re => re.expirationFee = none) and
	(re.expirationFee = none => ri2.reservation = re)
	
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
	passengers >= 0 and passengers <= 4 and
	TimePrecedent [finishTime, startTime]
}

fact sameReservationAndRideClient
{
	all ri:Ride | ri.client = ri.reservation.client
}

fact rideFollowsReservation
{
	all ri:Ride |  TimePrecedent [ri.startTime, ri.reservation.time]
}

fact userWhoReservesPays
{
	all ri:Ride | ri.payment.client = ri.client and
	all re:Reservation | re.expirationFee != none implies re.expirationFee.client = re.client
}

sig Payment
{
	charge: one Int, //should be float
	client: one Client,
	dateTime: one DateTime
}

fact payOnlyReservationFeeOrRide
{
	no p: Payment | some re: Reservation, ri : Ride | re.expirationFee = p and ri.reservation = re
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
{second >= 0 and second <= 59}
/*{
	( 0 <= second and second <= 59) and
	( 0 <= minute and minute <= 59) and
	( 0 <= hour and hour <= 23) and
	( 1 <= day) and
	( 1 <= month and month <= 12) and
	( ( ( month = 11 or month = 4 or month = 6 or month = 9 ) implies day <= 30) and
		( ( month = 1 or month = 3 or month = 5 or month = 7 or month = 8 or month = 10 or month = 12 ) implies day <= 31 )) // and
		//( (month = 2 and year - ( ( year / 4 ) * 4 ) != 0 ) implies day <= 28 ) and  anno non bisestile
		//((month = 2 and year - ( ( year / 4 ) * 4 ) = 0) implies day <= 29)  ) anno bisestile 
}*/

pred TimePrecedent [ u1, u2: DateTime] //	 u1 succedes u2
{
	( u1.year > u2.year ) or
	( u1.year = u2.year and u1.month > u2.month ) or
	( u1.year = u2.year and u1.month = u2.month and u1.day > u2.day) or
	( u1.year = u2.year and u1.month = u2.month and u1.day = u2.day and u1.hour > u2.hour ) or
	( u1.year = u2.year and u1.month = u2.month and u1.day = u2.day and u1.hour = u2.hour and u1.minute > u2.minute ) or
	( u1.year = u2.year and u1.month = u2.month and u1.day = u2.day and u1.hour = u2.hour  and u1.minute = u2.minute and u1.second > u2.second ) 
}

pred show{}
run show for 3 but 12 int
