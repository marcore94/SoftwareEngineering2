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

one sig MediumHighBatteryLevel extends BatteryLevel
{}

one sig MediumLowBatteryLevel extends BatteryLevel
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
	all car:Car | ( car.state = Maintenance ) implies
	( ( car.driver = none ) and
	( ( car.batteryLevel = LowBatteryLevel or car.batteryLevel = EmptyBatteryLevel ) and ( car.charging = False ) ) and
	( one safeArea : SafeArea | InsideArea[car, safeArea] ) )
}

fact carInMaintenanceOutOfChargingArea
{
	all c: Car | c.state = Maintenance implies no ca: ChargingArea | c.actualPosition in ca.positions
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
	( c.driver != Operator implies one re : Reservation | re.reservedCar = c and re.client = c.driver ) )
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

sig Notification
{
	operator: lone Operator,
	car: one Car
}

fact oneNotificationPerOperatorAndCar
{
	all disjoint n1, n2: Notification | n1.operator != n2.operator and n1.car != n2.car
}

fact operatorNotifiedWhenDrives
{
	all c: Car | (c.driver in Operator and c.driver != none) implies (one n: Notification | n.car = c and n.operator = c.driver)	
}

fact operatorNotifiedForManteinance
{
	all c: Car | c.state = Maintenance implies one n: Notification | n.car = c
}

fact nearestOperator
{
	all n: Notification | n.car.actualPosition != n.operator.actualPosition implies no o: Operator | o.actualPosition = n.car.actualPosition
}

fact operatorInSameCarPositionForChargeOnSite
{
	(all n: Notification | n.car.charging = True implies n.operator.actualPosition = n.car.actualPosition) and
	(all n: Notification | n.operator.actualPosition = n.car.actualPosition and n.car.state = Maintenance implies n.car.charging = True)
}

fact carsInMaintenanceIfLowBattery
{
	all car : Car | ( ( ( car.batteryLevel = LowBatteryLevel or car.batteryLevel = EmptyBatteryLevel ) and ( car.charging = False ) ) and
	( one safeArea : SafeArea | InsideArea[car, safeArea] ) and
	( car.driver = none ) ) implies
	car.state = Maintenance
}

pred FreeOperator[ o : Operator]
{
	no n : Notification | n.operator = o
}

fact pendingNotifications
{
	all n : Notification | ( ( n.operator != none ) or ( n.operator = none and  ( no o : Operator | FreeOperator[ o ] ) ) ) and
	not (  ( n.operator != none ) and ( n.operator = none and  ( no o : Operator | FreeOperator[ o ] ) )  )
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
	reservedCar: lone Car,
	expirationFee: lone Payment,
	expired: one Bool
}
{
	( expired = True implies ( reservedCar = none and expirationFee != none) ) and
	( expired = False implies ( expirationFee = none  ) )
}

fact oneReservationPerCar
{
	all disjoint r1, r2: Reservation | ( r1.expired = False and r2.expired = False ) implies r1.reservedCar != r2.reservedCar 
}

fact oneActiveReservationPerClient
{
	all disjoint r1, r2 : Reservation | ( r1.expired = False and r2.expired = False ) implies r1.client != r2.client
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
	payment: lone Payment,
	finished: one Bool
}
{
	( passengers >= 0 and passengers <= 4 ) and
	( finished = True implies ( payment != none and reservation.reservedCar = none and reservation.expired = False ) ) and
	( finished = False implies ( payment = none and reservation.reservedCar != none and reservation.expired = False  ) )
}

fact atMostOneRideForReservation
{
	all disjoint r1, r2: Ride | r1.reservation != r2.reservation
}

pred relatedRideExists [re : Reservation]
{
	one ri : Ride | ri.reservation = re
}

fact sameRiderThatReserved
{
	all ri : Ride | ri.reservation.client = ri.client
}

fact carStateWhileReserved
{
	( all c : Car | c.state = Reserved implies one re : Reservation | re.reservedCar = c and not relatedRideExists[re] ) and
	( all re : Reservation | ( not relatedRideExists[re] and re.expired = False ) implies one c : Car | re.reservedCar = c )
}

fact carStateWhileInUse
{
	( all ri : Ride | ri.finished = False implies ri.reservation.reservedCar.state = InUse )
}

/*fact carStateWhileFree
{
	all c : Car | ( c.driver = none and ( one sa : SafeArea | c.actualPosition in sa.positions ) and ( no re : Reservation | re.reservedCar = c ) ) implies (c.state = Free)
}*/

abstract sig Discount
{
	amount : one Int	
}
{
	amount >0 and amount <100
}

one sig MoreThan2Passengers extends Discount
{}

fact moreThan2PassengersCondition
{
	all ri:Ride, m2p: MoreThan2Passengers | m2p in ri.payment.discounts iff ri.passengers >=2
} 

one sig EnoughBatteryLeft extends Discount
{}

fact enoughBatteryLeftCondition
{
	all ri: Ride, eBL: EnoughBatteryLeft | eBL in ri.payment.discounts iff 
	(ri.finished = True and ri.reservation.reservedCar.batteryLevel in
	(MediumHighBatteryLevel + HighBatteryLevel))
}

one sig CarPutInCharge extends Discount
{}

fact carPutInChargeCondition
{
	all ri:Ride, cPC: CarPutInCharge | cPC in ri.payment.discounts iff
	(ri.finished = True and one ca:ChargingArea | InsideArea[ri.reservation.reservedCar, ca] and 
	ri.reservation.reservedCar.charging = True)
}

sig Payment
{
	client: one Client,
	discounts : set Discount,
	appliedDiscount : lone Discount
}
{
	appliedDiscount in discounts
}

fact paymentIsUnique
{
	( all disjoint ri1, ri2 : Ride | ri1.payment != ri2.payment or ( ri1.payment = none and ri2.payment = none ) ) and
	( all disjoint re1, re2 : Reservation | re1.expirationFee != re2.expirationFee or ( re1.expirationFee = none and re2.expirationFee = none  ) ) and
	( all ri : Ride, re : Reservation | re.expirationFee != ri.payment or (re.expirationFee = none and ri.payment = none ) )
}

fact noStandalonePayments
{
	all p : Payment | ( one re : Reservation | re.expirationFee = p ) or ( one ri : Ride | ri.payment = p )
}

fact positionOutSafeArea
{
	some position: Position | all sa: SafeArea | position not in sa.positions
}

fact clientThatReservesPay
{
	( all r : Ride |  r.finished = True implies r.client = r.payment.client  ) and
	( all re : Reservation | re.expired = True implies re.client = re.expirationFee.client )
}

fact onlyOneDiscountApplied
{
	all re:Reservation, ri:Ride | re.expired = True implies 
		re.expirationFee.discounts = none and
		(#ri.payment.discounts >0 implies all d:Discount| d in ri.payment.discounts and  
		ri.payment.appliedDiscount.amount >= d.amount)
}

fact discountOnlyOnRide
{
	all reservation : Reservation | ( reservation.expired = True ) implies ( reservation.expirationFee.appliedDiscount = none and #(reservation.expirationFee.discounts) = 0 )
}

//prova soluzione
fact pdd
{
	all re : Reservation | ( re.expired = False ) implies (  ( re.reservedCar.state = Reserved or ( one r : Ride | ( r.finished = False and r.reservation = re ) ) ) and not ( re.reservedCar.state = Reserved and ( one r : Ride | ( r.finished = False and r.reservation = re ) ) ) )
}

assert a
{
	//no n : Notification | (n.operator != none) and ( one sa : SafeArea | n.car.actualPosition in sa.positions) and (n.car.state = Maintenance)
	no car : Car | car.driver in Client and (not (carIsInUse[car])) and car.driver != none
}

pred carIsInsideSafeArea [car : Car]
{
	one safeArea : SafeArea | InsideArea [car, safeArea]
}

pred carIsInUse [car : Car]
{
	one ride : Ride | ride.finished = False and ride.reservation.reservedCar = car
}

pred carNeedsMaintenance [ c : Car ]
{
	//provvisorio, suppone che la notifica venga creata sempre correttamente e che non rimanga in giro dopo che c'è stato l'intervento dell'operatore
	one notification : Notification | notification.car = c
}

pred notificationIsPending [ notification : Notification ]
{
	notification.operator = none
}

assert goalG4
{
	no disjoint reservation1, reservation2 : Reservation | reservation1.expired = False and reservation2.expired = False and reservation1.client = reservation2.client
}

assert goalG5
{
	all reservation : Reservation | reservation.expired = True implies reservation.reservedCar  = none
}

assert goalG6
{
	all ride : Ride | ( ride.finished = False and ( no notification : Notification | notification.car = ride.reservation.reservedCar ) ) implies ( ride.client = ride.reservation.client and ride.client = ride.reservation.reservedCar.driver )
}

assert goalG7
{
	all ride : Ride | ride.finished = True implies ( one payment : Payment | payment.client = ride.client )
}

assert goalG9
{
	all ride : Ride | ride.finished = True implies ( ( ( carIsInsideSafeArea [ ride.reservation.reservedCar ] ) or ( carIsInUse [ ride.reservation.reservedCar ] ) ) and not ( ( carIsInsideSafeArea [ ride.reservation.reservedCar ]  ) and ( carIsInUse [ ride.reservation.reservedCar ] ) ) )
}

/*
DA RIVEDERE
assert goalG11
{
	 all c : Car | ( carNeedsMaintenance [ c ] ) implies ( ( ( one o : Operator , notification : Notification | notification.operator != none and notification.operator = o and notification.car = c ) or ( one notification : Notification | notificationIsPending [ notification ] ) ) and not
	( ( one o : Operator , notification : Notification | notification.operator != none and notification.operator = o and notification.car = c ) and ( one notification : Notification | notificationIsPending [ notification ] ) ) )
}*/

pred show{}
//check goalG4 // controllato corretto
//check goalG5 //controllato corretto
//check goalG6 // controllato corretto
//check goalG7 // controllato corretto
//check goalG9 // controllato corretto
//check goalG11
//check a // controllato corretto
run show for 3
