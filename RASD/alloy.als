open util/boolean

/** Signatures **/

/* Atomic */
sig Slot {}
// sig CreditCard {}
sig License{
	isExpired: one Bool
}
sig DiscountSanction {}

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

/* Emergency report */
enum ERStatus { // remove if not needed
	EROpen, ERDispatched, ERWip, ERClosed, ERCantClose // FIXME give a check here
}
enum ERType { // remove if not needed
	ERAccident, EROnsite, ERNotOnsite // FIXME give a check here
}

/* User */
abstract sig GeneralUser {}
sig Guest extends GeneralUser {}
sig User extends GeneralUser {
	license: one License,
	banned: one Bool,
	active: one Bool, // commodity - true if not banned and license not exipred
	near: some Car
} {
	active = True <=> (banned = True or license.isExpired = True)
}

/* Parking area */
abstract sig GeneralParkingArea {
//	slot: set Slot,
	capacity: one Int,
	cars: set Car
} {
//	#car <= #slot
	#cars <= capacity
	// TODO slots cannot be shared by parking areas! --> remove Slots!
}
sig ParkingArea extends GeneralParkingArea {}
sig ChargingArea extends GeneralParkingArea {
	// TODO sth here?
}

/* Car */
sig Car {
	reserved: one Bool,
	inUse: one Bool,
	battery: one BatteryStatus,
	parkedIn: lone GeneralParkingArea,
	isCharging: one Bool
} {
	isCharging = True => ( parkedIn != none and parkedIn in ChargingArea)
	inUse = True <=> parkedIn = none // car either parked or in use
	reserved = True => parkedIn != none
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
	chargeChanges: some DiscountSanction,
	moneySavingOption: one Bool
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

	all c : Car | ( c.reserved = True <=> (some r : Reservation | c = r.car) )
	all c : Car | ( c.inUse = True <=> (some r : Ride | c = r.car) )
}

fact CarUsageExclusivity {
	all c : Car | ( lone res : Reservation | res.car = c ) // every car is in 0..1 reservation
	all c : Car | ( lone ride : Ride | ride.car = c ) // every car is in 0..1 ride
	Reservation.car & Ride.car = none // no car both reserved and in ride
	all u : User | ( lone res : Reservation | res.user = u ) // every user has 0..1 reservation
	all u : User | ( lone ride : Ride | ride.user = u ) // every user has 0..1 ride
	Reservation.user & Ride.user = none // no user with both a reservation and a current ride
}

pred show { }
run show
