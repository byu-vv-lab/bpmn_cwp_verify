//**********VARIABLE DECLARATION************//
bool f = true
bool old_f = f

//**********CWP VARIABLE DECLARATION************//
bool StartState = false
bool End = false
//**********************************************//

inline updateState() {
	bool StartState_prime = (f == true) && !(f == false)
	bool End_prime = (f == false) && !(false)
	if
		:: StartState && End_prime
		:: StartState && StartState_prime
		:: End && End_prime
		:: else -> printf("Assert: Not a valid CWP transition"); assert false
	fi
	StartState = StartState_prime
	End = End_prime
	// Verification of properties 1 & 2 (verifying that we are always in one state and only one state)
	int sumOfActiveStates = StartState + End

	if
		:: (sumOfActiveStates != 1) -> {printf("Assert: In more that one or no state"); assert false}
		:: else -> skip
	fi
}
inline caculateState() {
	StartState = (f == true) && !(f == false)
	End = (f == false) && !(false)
}
inline stateLogger(){
	printf("Changed Vars: \n")
	if
		:: f != old_f ->
			printf("f = %e\n", f)
			old_f = f
		:: else
	fi;
	if
		:: StartState == true ->
			printf("Current state: StartState\n")
		:: else
	fi;
	if
		:: End == true ->
			printf("Current state: End\n")
		:: else
	fi;
}
inline stateDump(){
	printf("f = %d\n", f)
}
#define hasToken(place) (place != 0)

inline putToken(place) {
	if
		:: place != 1 -> place = 1
		:: else -> {
			printf("Assert: Attempting to place token in already-occupied place\n")
			assert false
		}
	fi
}

#define consumeToken(place) place = 0


bit Event_1hvprlj = 0
bit Activity_0rhvnxh_FROM_Event_1hvprlj = 0
bit Event_0376xz1_FROM_Activity_0rhvnxh = 0
bit Event_0376xz1_FROM_Activity_0h2q9nt = 0
bit Event_09x61bg_FROM_Event_0376xz1 = 0
bit Event_0nkdqiv = 0
bit Event_1npgp03_FROM_Event_0nkdqiv = 0
bit Event_1npgp03_FROM_Activity_0rhvnxh = 0
bit Activity_0h2q9nt_FROM_Event_1npgp03 = 0
bit Event_0rlxl7u_FROM_Activity_0h2q9nt = 0
inline Event_1hvprlj_BehaviorModel() {
	skip
}

inline Activity_0rhvnxh_BehaviorModel() {
	skip
}

inline Event_0376xz1_BehaviorModel() {
	skip
}

inline Event_09x61bg_BehaviorModel() {
	skip
}

inline Event_0nkdqiv_BehaviorModel() {
	skip
}

inline Event_1npgp03_BehaviorModel() {
	skip
}

inline Activity_0h2q9nt_BehaviorModel() {
	skip
}

inline Event_0rlxl7u_BehaviorModel() {
	skip
}

init {
	atomic {
		stateDump()
		caculateState()
		run Process_1r9euto()
		run Process_1xc3pol()
	}
}

proctype Process_1r9euto() {
	d_step {
		printf("ID: Process_1r9euto\n")
		stateLogger()
		pid me = _pid
		putToken(Event_1hvprlj)
	}
	do
	:: atomic { ((hasToken(Event_1hvprlj))) ->
		Event_1hvprlj_BehaviorModel()
		d_step {
			printf("ID: Event_1hvprlj\n")
			stateLogger()
			consumeToken(Event_1hvprlj)
			putToken(Activity_0rhvnxh_FROM_Event_1hvprlj)
		}
	}
	:: atomic { ((hasToken(Activity_0rhvnxh_FROM_Event_1hvprlj))) ->
		Activity_0rhvnxh_BehaviorModel()
		d_step {
			printf("ID: Activity_0rhvnxh\n")
			stateLogger()
			consumeToken(Activity_0rhvnxh_FROM_Event_1hvprlj)
			putToken(Event_0376xz1_FROM_Activity_0rhvnxh)
			putToken(Event_1npgp03_FROM_Activity_0rhvnxh)
		}
	}
	:: atomic { ((hasToken(Event_0376xz1_FROM_Activity_0rhvnxh)) && (hasToken(Event_0376xz1_FROM_Activity_0h2q9nt))) ->
		Event_0376xz1_BehaviorModel()
		d_step {
			printf("ID: Event_0376xz1\n")
			stateLogger()
			consumeToken(Event_0376xz1_FROM_Activity_0rhvnxh)
			consumeToken(Event_0376xz1_FROM_Activity_0h2q9nt)
			putToken(Event_09x61bg_FROM_Event_0376xz1)
		}
	}
	:: atomic { ((hasToken(Event_09x61bg_FROM_Event_0376xz1))) ->
		Event_09x61bg_BehaviorModel()
		d_step {
			printf("ID: Event_09x61bg\n")
			stateLogger()
			consumeToken(Event_09x61bg_FROM_Event_0376xz1)
		}
		break
	}
	od
}
proctype Process_1xc3pol() {
	d_step {
		printf("ID: Process_1xc3pol\n")
		stateLogger()
		pid me = _pid
		putToken(Event_0nkdqiv)
	}
	do
	:: atomic { ((hasToken(Event_0nkdqiv))) ->
		Event_0nkdqiv_BehaviorModel()
		d_step {
			printf("ID: Event_0nkdqiv\n")
			stateLogger()
			consumeToken(Event_0nkdqiv)
			putToken(Event_1npgp03_FROM_Event_0nkdqiv)
		}
	}
	:: atomic { ((hasToken(Event_1npgp03_FROM_Event_0nkdqiv)) && (hasToken(Event_1npgp03_FROM_Activity_0rhvnxh))) ->
		Event_1npgp03_BehaviorModel()
		d_step {
			printf("ID: Event_1npgp03\n")
			stateLogger()
			consumeToken(Event_1npgp03_FROM_Event_0nkdqiv)
			consumeToken(Event_1npgp03_FROM_Activity_0rhvnxh)
			putToken(Activity_0h2q9nt_FROM_Event_1npgp03)
		}
	}
	:: atomic { ((hasToken(Activity_0h2q9nt_FROM_Event_1npgp03))) ->
		Activity_0h2q9nt_BehaviorModel()
		d_step {
			printf("ID: Activity_0h2q9nt\n")
			stateLogger()
			consumeToken(Activity_0h2q9nt_FROM_Event_1npgp03)
			putToken(Event_0rlxl7u_FROM_Activity_0h2q9nt)
			putToken(Event_0376xz1_FROM_Activity_0h2q9nt)
		}
	}
	:: atomic { ((hasToken(Event_0rlxl7u_FROM_Activity_0h2q9nt))) ->
		Event_0rlxl7u_BehaviorModel()
		d_step {
			printf("ID: Event_0rlxl7u\n")
			stateLogger()
			consumeToken(Event_0rlxl7u_FROM_Activity_0h2q9nt)
		}
		break
	}
	od
}
