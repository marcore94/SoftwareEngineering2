open util/boolean

sig Position
{}

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
	email: one Email,
	actualPosition: one Position
}

sig Email
{}

fact oneMailPerUser
{
	all e: Email | one user : User | user.email = e
}

fact noUserInSamePosition
{
	all disjoint u1, u2: User | u1.actualPosition != u2.actualPosition
}

fact emailIsUnique
{
	all disjoint u1,u2: User | u1.email != u2.email
}

sig Client extends User
{}

sig Operator extends User
{}

sig Car
{
	charging: one Bool,
	driver: lone User,
	actualPosition: one Position,
	code: one Code,
	batteryLevel: one BatteryLevel,
	state: one CarState
}

sig Code
{}

fact everyCodeAssignedToCar
{
	all c: Code | one car: Car | car.code = c
}

abstract sig BatteryLevel
{}

one sig HighBatteryLevel extends BatteryLevel
{}

one sig MediumBatteryLevel extends BatteryLevel
{}

one sig LowBatteryLevel extends BatteryLevel
{}

one sig EmptyBatteryLevel extends BatteryLevel
{}

fact atMostOneCarForDriver
{
	all disjoint c1, c2 : Car | ( c1.driver != none and c2.driver != none ) implies c1.driver != c2.driver
}

fact noCarsInSamePosition
{
	all disjoint c1, c2: Car | c1.actualPosition != c2.actualPosition
}

abstract sig CarState
{}

one sig Free extends CarState
{}

one sig Reserved extends CarState
{}

one sig InUse extends CarState
{}

one sig Maintenance extends CarState
{}

fact carNotReservableDuringMaintenance 
{
	all car:Car | car.state = Maintenance implies no re : Reservation | re.reservedCar = car
}

fact carNotDrivableDuringMaintenance
{
	all car:Car | car.state = Maintenance implies car.driver = none
}

fact chargingConditions
{
	all car: Car | car.charging = True implies (car.state = Free or car.state = Reserved 
	or car.state = Maintenance) //per includere ricarica in loco
}

fact noUserWhileFreeOrReserved
{
	all c: Car | (c.state = Free or c.state = Reserved) implies c.driver = none
}

fact driverInsideWhileDriving
{
	all c: Car | c.state = InUse implies ( c.driver != none and c.actualPosition = c.driver.actualPosition and 
	(c.driver != Operator implies one re : Reservation | re.reservedCar = c and re.client = c.driver)) 
}

fact codesOfTheCarsAreUnique
{
	all c1, c2: Car | (c1!=c2)=>c1.code!=c2.code
}

fact carStateInSafeArea
{
	all car: Car | (car.state = Free or car.state = Reserved) implies 
	some safeArea: SafeArea | InsideArea[car, safeArea]
}

fact noEnergyLawViolation
{
	all car: Car | car.batteryLevel = EmptyBatteryLevel implies 
	(car.state != InUse and car.state != Reserved)
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
	all c : Car, ca: ChargingArea |( c in ca.chargingCars ) iff c.charging = True 
}

sig Reservation
{
	client: one Client,
	reservedCar: one Car,
	expirationFee: lone Payment
}

fact oneReservationPerClient
{
	all r1: Reservation, r2: Reservation | r1.client = r2.client implies r1 = r2
}

fact oneReservationPerCar
{
	all r1: Reservation, r2: Reservation | r1.reservedCar = r2.reservedCar implies r1 = r2
}

fact reservationExpiresOrThereIsRide
{
	all re:Reservation, ri1 : Ride | one ri2:Ride | 
	( ri1.reservation = re => re.expirationFee = none) and
	((re.expirationFee = none and re.reservedCar.state != Free) => ri2.reservation = re)
	
}

fact noReservationWithOutOfBatteryCars
{
	all r: Reservation | r.reservedCar.batteryLevel != LowBatteryLevel and  r.reservedCar.batteryLevel != EmptyBatteryLevel
}

sig Ride
{
	client: one Client,
	reservation: one Reservation,
	passengers: one Int,
	payment: one Payment
}
{
	passengers >= 0 and passengers <= 4
}

fact sameReservationAndRideClient
{
	all ri:Ride | ri.client = ri.reservation.client
}

fact carDriverIsTheReservationClient
{
	all ri:Ride | ri.reservation.reservedCar.driver = ri.reservation.client
}

fact userWhoReservesPays
{
	all ri:Ride | ri.payment.client = ri.client and
	all re:Reservation | re.expirationFee != none implies re.expirationFee.client = re.client
}

abstract sig Discount
{
	amount : one Int	
}

sig MoreThan2Passengers extends Discount
{}

fact moreThan2PassengersCondition
{
	all ri:Ride, m2p: MoreThan2Passengers | m2p in ri.payment.discounts implies ri.passengers >=2
} 

sig Payment
{
	client: one Client,
	discounts : set Discount,
	appliedDiscount : one Discount
}
{
	appliedDiscount in Discount
}

fact payOnlyReservationFeeOrRide
{
	no p: Payment | some re: Reservation, ri : Ride | re.expirationFee = p and ri.reservation = re
}

fact positionOutSafeArea
{
	some position: Position | all sa: SafeArea | position not in sa.positions
}

pred show{}
run show for 3
