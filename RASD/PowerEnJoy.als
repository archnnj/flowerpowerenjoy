open util/boolean

sig Date{	
	day: one Int,
	month: one Int,
	year: one Int
}{
	day>0, day<=31,
	month>0, month<=12,
	year>1910
}
sig Location{}
sig Time{}
sig Slot{}
sig Bool {}

/*enum CarStatus{
	AVAILABLE,
	RESERVED,
	INUSE
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
	cStatus: one Bool,
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


sig Ride {
	rStatus: one RequestStatus,
	firstLocation: one Location,
	lastLocation: one Location,
	car: one Car	,
	user: one User,
	passengers: one Int,
	durationInMins: one Int,
	chargePerMinute: one Int,
	moneySavingOption: one Bool,
	discount: one Int,
	sanction: one Int
}{
	firstLocation != lastLocation,
	durationInMins>0,
	chargePerMinute>0,
	passengers>=0,
	passenger<=3
}

sig Reservation {
	car: one Car,
	user: one User,
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



