open util/boolean

/** Signatures **/

/* Atomic */
sig Slot {}
// sig CreditCard {}
sig License{
	isExpired: one Bool
}
sig Passenger {}

/* Internal actors */
sig Admin {} // needed?
sig Operator {
	// location?
}

/* Battery status */
// abstract sig BatteryStatus {}
// one sig BatteryLow extends BatteryStatus {} // below 20% ?
// one sig BatteryHigh extends BatteryStatus {} // above 50% ?
enum BatteryStatus {
	BatteryLow, BatteryHigh
}

/* Emergency report enums */
enum ERStatus { // remove if not needed
	EROpen, ERDispatched, ERWip, ERClosed, ERCantClose // FIXME give a check here
}
enum ERType { // remove if not needed
	ERAccident, EROnsite, ERNotOnsite // FIXME give a check here
}

/* Car status */
enum CarStatus {
	Available, Reserved, InUse, OutOfOrder
}

/* Discounts and Sanctions */
abstract sig DiscountSanction { }
abstract sig DiscountSanctionPerMinute extends DiscountSanction { }
sig PassengersDiscount extends DiscountSanctionPerMinute { }
abstract sig DiscountSanctionWholeRide extends DiscountSanction {}
sig HighBatteryDiscount extends DiscountSanctionWholeRide { }
sig PlugInDiscount extends DiscountSanctionWholeRide { }

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
//	slot: set Slot,
	capacity: one Int,
	cars: set Car
} {
//	#car <= #slot
	capacity > 0
	#cars <= capacity
	// TODO slots cannot be shared by parking areas! --> remove Slots!
}
sig ParkingArea extends GeneralParkingArea {}
sig ChargingArea extends GeneralParkingArea {
	// TODO sth here?
}

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
	isCharging = True => ( parkedIn != none and parkedIn in ChargingArea) // isCharging only if in charging area
	parkedIn = none <=> ( status = OutOfOrder or ( status = InUse and this[Ride<:car].timeWindowActive = False ) ) // car not parked can either be out of order or in use (exluded during time window)
	status = Reserved => parkedIn != none // reserved only if parked
	status in (Available + Reserved + OutOfOrder) => driverInside = False // no driver inside if the car is not in use
	engineOn = True => status in (InUse + OutOfOrder)
}

/* User interactions*/
sig Reservation {
	user: one User,
	car: one Car,
	// beginning, etc --> can't describe it in static model!! :S
}
sig Ride {
	user: one User,
	car: one Car,
	moneySavingOption: one Bool,
	passengers: set Passenger,
	timeWindowActive: one Bool,
	chargesRunning: one Bool,
	discSanctApplicableNow: set DiscountSanction,
	discSanctApplicableRide: set DiscountSanction
} {
	#passengers < 4 // capacity of cars (1 driver + 3 passengers)
}
sig EmergencyReport {
	user: lone User, // can be generated by the system too
	assignedOp: lone Operator,
	car: one Car,
	status: one ERStatus,
	type: one ERType // needed?
} {
	assignedOp = none <=> status = EROpen // assignedOp empty iff status is EROpen
}

/** Facts **/

/* Structural constraints */

fact AttrbutePairings {
	Car<:parkedIn = ~(GeneralParkingArea<:cars) // Car::parkedIn = transpose of GeneralParkingArea::cars

	no disjoint u1, u2 : User | u1.license = u2.license // license is personal
	User.license = License // not consider licenses of people outside the system

	all c : Car | ( c.status = Reserved <=> (some r : Reservation | c = r.car) )
	all c : Car | ( c.status = InUse <=> (some r : Ride | c = r.car) )
}

fact exclusivity {
	all c : Car | ( lone res : Reservation | res.car = c ) // every car is in 0..1 reservation
	all c : Car | ( lone ride : Ride | ride.car = c ) // every car is in 0..1 ride
	Reservation.car & Ride.car = none // no car both reserved and in ride
	all u : User | ( lone res : Reservation | res.user = u ) // every user has 0..1 reservation
	all u : User | ( lone ride : Ride | ride.user = u ) // every user has 0..1 ride
	Reservation.user & Ride.user = none // no user with both a reservation and a current ride

	all disjoint r1, r2 : Ride | r1.passengers & r2.passengers = none
}

/* Requirements */

// G[1] The system allows guests to register; to complete the registration procedure the system sends a password to the guest as an access key.
fact RegistrationRequirements {
	// none // TODO ?
}

// G[2] The system should enable a registered user to find the location of an available car within a certain distance from the user’s location or from a specified address.
fact LocalizationRequirements {
	// none // TODO ?
}

// G[3] The system enables user to reserve a single available car in a certain geographical region for one hour before the user picks it up. If the car is not picked up by that time, the reservation expires, the system tags this car as available again and it charges the user a fine of 1 EUR.
fact ReservationRequirements {
	no userWithRes : Reservation.user | userWithRes.license.isExpired = True // reservation only for user with valid license
	no userWithRes : Reservation.user | userWithRes.banned = True // no banned user can reserve a car
}

// G[4] The system should allow the user to employ a car in a proper and safe way.
fact RideRequirements {
	// car unlocked only if user with reservation or which is using it is near it
	all c : Car |
		c.locked = False =>
			( some u : User , r : Reservation | r.user = u and r.car = c and c in u.near ) or
			( some u : User , r : Ride | r.user = u and r.car = c and c in u.near )

	// car locked if user has exited it inside a safe area
	all c : Car |
		(
			c.parkedIn != none and
			c.driverInside = False and
			( c in Ride.car => #( ((Ride<:car).c).passengers ) = 0 )  // c has no passengers (if it is in a ride, otherwise this is not considered)
			=>
			c.locked = True
		)

	// time window definition
	all r : Ride | let c = r.car | r.timeWindowActive = True => c.parkedIn != none // time window only if car in parking area
}

// G[5] The system charges the user for a predefined amount of money per minute. A screen on the car notifies the user of the current charges.
fact ChargesRequirements {
	// none
}

// G[6] The system starts charging the user as soon as the car ignites. It stops charging them when the car is parked in a safe area and the user exits the car.
fact ChargingRequirements {
	all r : Ride | let c = r.car | ( c.status = InUse and c.engineOn = True ) => r.chargesRunning = True
	all r : Ride | let c = r.car | ( c.parkedIn != none and c.driverInside = False ) => r.chargesRunning = False // charges stops when user exits the car in a safe area (or haven't entered yet)
	all r : Ride | r.timeWindowActive = True => r.chargesRunning = False // no charges in time window
}

// G[7] The system should encourage good user behaviour through the application of discounts to the fee per minute.
fact DiscountsRequirements {
	all r : Ride | PassengersDiscount in r.discSanctApplicableNow <=> #r.passengers >= 2 and r.car.engineOn = True // R[7.3] discount for rides with two or more passengers
	all r : Ride | HighBatteryDiscount in r.discSanctApplicableRide <=> r.timeWindowActive = True and r.car.battery = BatteryHigh // R[7.4] discount if more than 50% battery at end of the ride
	all r : Ride | PlugInDiscount in r.discSanctApplicableRide <=> r.timeWindowActive = True and r.car.isCharging = True
	// NB: for simplicity here the ride is considered end when the time window is active. This does not affect the model.
}

assert DriverNeverTrapped {
	no c : Car | c.status != InUse and c.driverInside = True
}
// check DriverNeverTrapped

pred show {
//	(Car<:status).Available != none
//	(Car<:status).Reserved != none
//	(Car<:status).OutOfOrder != none
//	(Car<:status).InUse != none
//	Car.isCharging not in False
//	User.active = True
//	some r : Ride | r.timeWindowActive = True
//	some disj r1, r2 : Ride | #r1.passengers >= 2 and #r2.passengers >= 2xs
}
run show
