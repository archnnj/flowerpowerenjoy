open util/boolean

sig Date{}
sig Location{}
sig Time{}
sig Slot{}

/*enum CarStatus{
*	AVAILABLE,
*	RESERVED,
*	INUSE
}*/

enum UserStatus{
	SIGNEDIN,
	BANNED
}

enum RideStatus{
	WAITING,
	RUNNING,
	COMPLETE
}

sig CreditCard{
	cardNumber: one Int,
	expDate: one Date,
	cvv: one Int
}{
	cardNumber>0,
	cvv>0
}

sig EmergencyReport{
	date: one Date,
	type: one String,
	car: one Car,
	user: one User,
	operator: one Operator
}

sig Operator{
	firstname: one String,
	lastname: one String,
	location: one Location,
	emReport: set EmergencyReport
}

sig Admin{
	firstname: one String,
	lastname: one String,
	controlPanel: one ControlPanel
}

sig License{
	licenseNumber: one Int,
	issueDate: one Date,
	expirationDate: one Date,
	lStatus: one Bool
}{
	issueDate!=expirationDate
}

sig GenealUser{}

sig Guest extends GeneralUser{	
}

sig User extends GeneralUser{
	username : one String,
	password: one String,
	uStatus: one UserStatus,
	uRide: one Ride,
	uReservation: one Reservation,
	emReport: lone EmergencyReport
}{
	username!=password
}

sig Car {
	carPlate: one String,
	battery: one Int,
	available: one Bool,
	cRide: one Ride,
	cReservation: one Reservation,
	emReport: lone EmergencyReport 
}{
 	battery>=0,
	battery<=100
}

sig GeoZone {
	city: set Location
}{
	city>=3
}

sig AppliablePercent{
	percent: one Int
}{
	percent<=100
}

sig Discount extends AppliablePercent{
}{
	percent >1
}

sig Sanction extends AppliablePercent{
}{
	percent<-1
}

sig Ride {
	rStatus: one RideStatus,
	firstLocation: one Location,
	lastLocation: one Location,
	car: one Car	,
	user: one User,
	passengers: one Int,
	durationInMins: one Int,
	chargePerMinute: one Int,
	moneySavingOption: one Bool,
	discount: lone Discount,
	sanction: lone Sanction,
}{
	firstLocation != lastLocation,
	durationInMins>0,
	chargePerMinute>0,
	passengers>=0,
	passenger<=3, 
	rStatus = ACTIVE => discount = none and sanction = none 
	rStatus = WAITING <=> one c: Car | c.available = FALSE and c.cRide = this
}

sig Reservation {
	car: one Car,
	user: one User,
	ride: one Ride
	minutes: one Int
}{
	minutes>0,
	minutes<=60
}

sig GeneralParkingArea{
	location: set Location,
	slot: set Slot,
	car: set Car
}{
	#location>0
} 

sig ParkingArea extends GeneralParkingArea{
}

sig ChargingArea extends ChargingArea{
	pluggedCars: set Car
}

fact licenseAreUnique{
	all l1, l2 : license | (l1 != l2) => l1.licenseNumber != l2.licenseNumber
}

fact usernameAreUnique{
	all u1, u2: User | (u1 != u2) => u1.username != u2.username
}

fact carPlateAreUnique{
	all c1, c2 : Car | (c1 != c2) => c1.carPlate != c2.carPlate
}

fact userAssociationRide{
	all u: User, r: Ride | (r.user = u) iff (r in u.uRide)
}

fact carAssociationRide{
	all c: Car, r: Ride | (r.car = c) iff (r in c.cRide)
}

fact oneWaitingRunningRidePerUser{
	no u: User, r1, r2: Ride | (r1 != r2) and (r1.user =u) and (r2.user = u) and
	((r1.rStatus = WAITING or r1.rStatus = RUNNING) and (r2.rStatus = WAITING or r2.rStatus = RUNNING) )	
}

fact oneWaitingRunningRidePerCar{
	no c: Car, r1, r2: Ride | (r1 != r2) and (r1.car = c) and (r2.car = c) and
	((r1.rStatus = WAITING or r1.rStatus = RUNNING) and (r2.rStatus = WAITING or r2.rStatus = RUNNING) )
}

fact noActiveRideNoReservationForBannedUser{
	all u: User | u.uStatus = BANNED => (no ri: Ride | ri.rStatus = ACTIVE and ri.user = u) and (no re: Reservation | re.user = u)
}

/* only one RUNNING ride per user
* if ride is running => car is not available
* if car is not available => ride is running */
fact carInUseNotAvailable{
	all r: Ride, c: Car | (r.rStatus = RUNNING and r.user = c) => (c.available = FALSE)
	all c: Car | c.available = FALSE => (one ri: Ride | ri.rStatus = RUNNING and (ri.user = u))
}

fact userHasOnlyOneReservation{
	no r1 & r2 : Reservation | r1.user = r2.user
}

fact carHasOneReservation{
	no r1 & r2: Reservation | r1.car=r2.car
}

fact noCarForBannedUser{
	all u: User | u.uStatus = BANNED => (no r:Ride | (r.rStatus = ACTIVE or r.rStatus = WAITING) and r.user =u) and (no re: Reservation | re.user = u  )
}



