open util/boolean

/** Signatures **/

/* Atomic */
sig License{
	isExpired: one Bool
}
sig Passenger {}

/* Internal actors */
sig Operator {}

/* Battery status */
enum BatteryStatus {
	EmptyBattery, // < 3%
	BatteryLow, // 3% - 20%
	BatteryMedium, // 20% - 50%
	BatteryHigh // > 50%
}

/* Emergency report enums */
enum ERStatus {
	EROpen, ERDispatched, ERWip, ERClosed, ERCantClose
}
enum ERType {
	ERAccident, EROnsite, ERNotOnsite
}

/* Car status */
enum CarStatus {
	Available, Reserved, InUse, OutOfOrder
}

enum DistanceFromChargingArea {
	Far, Near // Far: more than 3km; Near: otherwise
}

/* Discounts and Sanctions types */
abstract sig DiscountSanctionPerMinute { }
sig PassengersDiscount extends DiscountSanctionPerMinute { }
abstract sig DiscountSanctionWholeRide { }
sig HighBatteryDiscount extends DiscountSanctionWholeRide { }
sig PlugInDiscount extends DiscountSanctionWholeRide { }
sig MoneySavingOptionDiscount extends DiscountSanctionWholeRide { }
sig FarChargingAreaSanction extends DiscountSanctionWholeRide { }
sig LowBatterySanction extends DiscountSanctionWholeRide { }

/* User */
abstract sig GeneralUser {}
sig Guest extends GeneralUser {}
sig User extends GeneralUser {
	license: one License,
	banned: one Bool,
	active: one Bool, // commodity - true if not banned and license not exipred
	near: set Car
} {
	active = False <=> (banned = True or license.isExpired = True)
}

/* Parking area */
abstract sig GeneralParkingArea {
	capacity: one Int,
	cars: set Car
} {
	capacity > 0
	#cars <= capacity
}
sig ParkingArea extends GeneralParkingArea {
	distanceChargingArea: one DistanceFromChargingArea
}
sig ChargingArea extends GeneralParkingArea { }

/* Car */
sig Car {
	battery: one BatteryStatus,
	parkedIn: lone GeneralParkingArea,
	isCharging: one Bool,
	status: one CarStatus,
	driverInside: one Bool,
	locked: one Bool, // doors locked/unlocked
	engineOn : one Bool
} {
	isCharging = True => ( parkedIn != none and parkedIn in ChargingArea) 
		// isCharging only if in charging area
	parkedIn = none <=> ( status = OutOfOrder or 
		( status = InUse and this[Ride<:car].timeWindowActive = False ) ) 
		// car not parked can either be out of order or in use (exluded during time window)
	status = Reserved => parkedIn != none // reserved only if parked
	status in (Available + Reserved + OutOfOrder) => driverInside = False 
		// no driver inside if the car is not in use
	engineOn = True => status in (InUse + OutOfOrder)
	battery = EmptyBattery => engineOn = False
	battery = EmptyBattery => status not in (Available + Reserved)
}

/* User interactions*/
sig Reservation {
	user: one User,
	car: one Car
}
sig Ride {
	user: one User,
	car: one Car,
	moneySavingOption: one Bool,
	moneySavingOptionSuggestion: lone GeneralParkingArea,
	passengers: set Passenger,
	timeWindowActive: one Bool,
	chargesRunning: one Bool,
	discSanctApplicableNow: set DiscountSanctionPerMinute,
	discSanctApplicableRide: set DiscountSanctionWholeRide,
	isStandard: one Bool 
		// ride finishes with the car being parked in a safe 
		// area and no emergency has occurred
} {
	#passengers < 4 // capacity of cars (1 driver + 3 passengers)
	moneySavingOptionSuggestion != none <=> moneySavingOption = True
	isStandard = False <=> some er : EmergencyReport | er.user = user and er.car = car
}
sig EmergencyReport {
	ride : one Ride,
	user: one User,
	assignedOp: lone Operator,
	car: one Car,
	status: one ERStatus,
	type: one ERType
} {
	user = ride.user
	car = ride.car
	assignedOp = none <=> status = EROpen // assignedOp empty iff status is EROpen
}

/** Facts **/

/* Structural constraints */

fact AttrbutePairings {
	Car<:parkedIn = ~(GeneralParkingArea<:cars) 
		// Car::parkedIn = transpose of GeneralParkingArea::cars

	no disjoint u1, u2 : User | u1.license = u2.license // license is personal
	User.license = License // not consider licenses of people outside the system

	all c : Car | ( c.status = Reserved <=> (some r : Reservation | c = r.car) )
	all c : Car | ( c.status = InUse <=> (some r : Ride | c = r.car) )

	all r : Ride | let u = r.user, c = r.car | ( c.driverInside  = True ) => ( u.near = c )
}

fact exclusivity {
	all c : Car | ( lone res : Reservation | res.car = c ) 
		// every car is in 0..1 reservation
	all c : Car | ( lone ride : Ride | ride.car = c ) 
		// every car is in 0..1 ride
	Reservation.car & Ride.car = none 
		// no car both reserved and in ride
	all u : User | ( lone res : Reservation | res.user = u ) 
		// every user has 0..1 reservation
	all u : User | ( lone ride : Ride | ride.user = u ) 
		// every user has 0..1 ride
	Reservation.user & Ride.user = none 
		// no user with both a reservation and a current ride

	all disjoint r1, r2 : Ride | r1.passengers & r2.passengers = none 
		// passengers no in more ride at the same time

	all disjoint e1, e2 : EmergencyReport | e1.ride & e2.ride = none 
		// no rides with more than one emergency report

	all disjoint e1, e2 : EmergencyReport | e1.assignedOp & e2.assignedOp = none 
		// operator can be assigned to one emergency report at a time
}

/* Requirements */

// G[1] The system allows guests to register; to complete the registration 
// procedure the system sends a password to the guest as an access key.
fact RegistrationRequirements {
	// none
}

// G[2] The system should enable a registered user to find the location of 
// an available car within a certain distance from the user’s location or 
// from a specified address.
fact LocalizationRequirements {
	// none
}

// G[3] The system enables user to reserve a single available car in a 
// certain geographical region for one hour before the user picks it up.
// If the car is not picked up by that time, the reservation expires, the system 
// tags this car as available again and it charges the user a fine of 1 EUR.
fact ReservationRequirements {
	// R[3.5] reservation only for user with valid license
	no userWithRes : Reservation.user | userWithRes.license.isExpired = True
	// R[3.6] no banned user can reserve a car
	no userWithRes : Reservation.user | userWithRes.banned = True
}

// G[4] The system should allow the user to employ a car in a proper and safe way.
fact RideRequirements {
	// R[4.9] car unlocked only if user with reservation or which is 
	// using it is near it
	all c : Car |
		c.locked = False =>
			( some u : User , r : Reservation | r.user = u and r.car = c and c in u.near ) or
			( some u : User , r : Ride | r.user = u and r.car = c and c in u.near )
	// R[4.10] car locked if user has exited it inside a safe area
	all c : Car |
		(
			c.parkedIn != none and
			c.driverInside = False and
			( c in Ride.car => #( ((Ride<:car).c).passengers ) = 0 )  
		// c has no passengers (if it is in a ride, otherwise this is not considered)
			=>
			c.locked = True
		)
	// R[4.12] time window definition (partial coverage of the requirement)
	all r : Ride | let c = r.car | r.timeWindowActive = True => c.parkedIn != none 
		// time window only if car in parking area
}

// G[5] The system charges the user for a predefined amount of money 
// per minute. A screen on the car notifies the user of the current charges.
fact ChargesRequirements {
	// none
}

// G[6] The system starts charging the user as soon as the car ignites. 
// It stops charging them when the car is parked in a safe area and the 
// user exits the car.
fact ChargingRequirements {
	// general requirement
	all r : Ride | let c = r.car | ( c.status = InUse and c.engineOn = True ) 
		=> r.chargesRunning = True
	// general requirement
	all r : Ride | r.timeWindowActive = True => r.chargesRunning = False
	// R[6.4] charges stops when user exits the car in a safe area 
	//(or haven't entered yet)
	all r : Ride | let c = r.car | ( c.parkedIn != none and c.driverInside = False ) 
		=> r.chargesRunning = False
}

// G[7] The system should encourage good user behaviour through the application 
// of discounts to the fee per minute.
fact DiscountsRequirements {
	// R[7.3] discount for rides with two or more passengers
	all r : Ride | PassengersDiscount in r.discSanctApplicableNow 
		<=> 
	#r.passengers >= 2 and r.car.engineOn = True
	// R[7.4] discount if more than 50% battery at end of a standard ride
	all r : Ride | HighBatteryDiscount in r.discSanctApplicableRide 
		<=> 
	r.timeWindowActive = True and r.car.battery = BatteryHigh and r.isStandard = True
	// R[7.5] discount if car plugged in at the end of the time window (approximation)
	all r : Ride | PlugInDiscount in r.discSanctApplicableRide 
		<=> 
	r.timeWindowActive = True and r.car.isCharging = True
	// NB: for simplicity here the ride is considered end when the time window 
	// is active. This does not affect the model.
}

// G[8] The system should discourage bad behaviour through the application 
// of sanctions to the fee per minute.
fact SanctionsRequirements {
	// R[8.1] sanction when car left at more than 3km from a charging area
	all r : Ride |
		FarChargingAreaSanction in r.discSanctApplicableRide
		<=>
		r.timeWindowActive = True and r.car.parkedIn in ParkingArea 
		and r.car.parkedIn.distanceChargingArea = Far
	// R[8.2] sanction if car left with less than 20% of battery
	all r : Ride |
		 LowBatterySanction in r.discSanctApplicableRide
		<=>
		r.timeWindowActive = True and r.car.battery = BatteryLow
	// NB: for simplicity here the ride is considered end when the time window 
	// is active. This does not affect the model.
}

// G[9] The system should provide an alternative usage mode for cars called 
// money saving option. Besides aiding the user in saving money, this mode 
// allows for a uniform distribution of cars throughout the city by suggesting the 
// user where to park.
fact MoneySavingOptionRequirements {
	// R[9.2] discount in money saving option if car returned in suggested area
	all r : Ride |
		MoneySavingOptionDiscount in r.discSanctApplicableRide
		<=>
		r.car.parkedIn = r.moneySavingOptionSuggestion
}

// G[10] The system allows the company to assist the users in case 
// of need and take care of the cars.
fact AssistanceMaintenanceRequirements {
	// none
}

/** Assertions **/

// Car assigned or reserved to the input User
fun carRelatedTo [u : User] : set Car {
	(( Ride<:user ).u ).car + (( Reservation<:user ).u ).car 
	// (set of cars related through Ride or Res for u)
}

// 1 if the driver is inside the car; 0 otherwise
fun driverCountInCarCapacity [c : Car] : one Int {
	c.driverInside = True =>1 else 0
}

assert carToSingleUser {
	// no car assigned to more than one user
	all disjoint u1, u2 : User |
		( u1.carRelatedTo & u2.carRelatedTo ) != none 
			=>
		u1.carRelatedTo != u2.carRelatedTo // if not both empty, then different)
}
check carToSingleUser

assert noReservationWithEmptyBatteryCar {
	// no car reserved with empty battery
	all r : Reservation | r.car.battery != EmptyBattery
}
check noReservationWithEmptyBatteryCar

assert driverNeverTrapped {
	// driver can't be inside a car if the car is not assigned to him
	no c : Car | c.status != InUse and c.driverInside = True
}
check driverNeverTrapped

assert carMaxCapacity {
	// car can't have more than 4 person inside
	all r : Ride | r.car.driverCountInCarCapacity + #r.passengers <= 4
}
check carMaxCapacity

/** Predicates **/

/* Domain assumptions */
pred DA {
	// everything has already been represented with the model itself
}

pred show {
	DA
}

run show
