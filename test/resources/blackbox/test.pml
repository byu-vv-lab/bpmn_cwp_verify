//**********VARIABLE DECLARATION************//
mtype:RiskState = {acceptable assessing notAcceptable riskInit}
mtype:CommunicationState = {communicationInit sent wait waiting}
mtype:ConditionsState = {changed conditionsInit same}
mtype:BlackBoxState = {blackBoxInit found missing}
mtype:SearchState = {off on searchInit}
mtype:RiskState risk = riskInit
mtype:RiskState old_risk = risk
mtype:CommunicationState uuvComms = communicationInit
mtype:CommunicationState old_uuvComms = uuvComms
mtype:ConditionsState conditions = conditionsInit
mtype:ConditionsState old_conditions = conditions
mtype:BlackBoxState blackBox = blackBoxInit
mtype:BlackBoxState old_blackBox = blackBox
mtype:SearchState search = searchInit
mtype:SearchState old_search = search

//**********CWP VARIABLE DECLARATION************//
bool InitState = true
bool PlanSearch = false
bool Deploy = false
bool ActiveSearch = false
bool RetrieveBlackBox = false
bool SearchOff = false
bool Return = false
//**********************************************//

inline updateState() {
    bool PlanSearch_prime = ((search == on) && (conditions == changed) && (risk == assessing)) && !((risk == acceptable && uuvComms == sent) || (risk == notAcceptable) || (search == off))
    bool Deploy_prime = ((risk == acceptable && uuvComms == sent)) && !((uuvComms == waiting && risk == acceptable))
    bool ActiveSearch_prime = ((uuvComms == waiting && risk == acceptable)) && !((conditions == changed) || (blackBox == found))
    bool RetrieveBlackBox_prime = ((blackBox == found)) && !((search == off))
    bool SearchOff_prime = ((search == off) && (search == off) && (search == off)) && !(false)
    bool Return_prime = ((risk == notAcceptable)) && !((risk == assessing) || (search == off))
    if
        :: InitState && PlanSearch_prime
        :: PlanSearch && Deploy_prime
        :: PlanSearch && Return_prime
        :: PlanSearch && SearchOff_prime
        :: PlanSearch && PlanSearch_prime
        :: Deploy && ActiveSearch_prime
        :: Deploy && Deploy_prime
        :: ActiveSearch && PlanSearch_prime
        :: ActiveSearch && RetrieveBlackBox_prime
        :: ActiveSearch && ActiveSearch_prime
        :: RetrieveBlackBox && SearchOff_prime
        :: RetrieveBlackBox && RetrieveBlackBox_prime
        :: SearchOff && SearchOff_prime
        :: Return && PlanSearch_prime
        :: Return && SearchOff_prime
        :: Return && Return_prime
        :: else -> assert false
    fi
    InitState = false
    PlanSearch = PlanSearch_prime
    Deploy = Deploy_prime
    ActiveSearch = ActiveSearch_prime
    RetrieveBlackBox = RetrieveBlackBox_prime
    SearchOff = SearchOff_prime
    Return = Return_prime
    // Verification of properties 1 & 2 (verifying that we are always in one state and only one state)
    int sumOfActiveStates = PlanSearch + Deploy + ActiveSearch + RetrieveBlackBox + SearchOff + Return

    if
        :: (sumOfActiveStates != 1) -> assert false
        :: else -> skip
    fi
}
inline stateLogger(){
    printf("Changed Vars: \n");
    if
        :: risk != old_risk ->
            printf("risk = %e\n", risk);
            old_risk = risk
        :: else -> skip
    fi;
    if
        :: uuvComms != old_uuvComms ->
            printf("uuvComms = %e\n", uuvComms);
            old_uuvComms = uuvComms
        :: else -> skip
    fi;
    if
        :: conditions != old_conditions ->
            printf("conditions = %e\n", conditions);
            old_conditions = conditions
        :: else -> skip
    fi;
    if
        :: blackBox != old_blackBox ->
            printf("blackBox = %e\n", blackBox);
            old_blackBox = blackBox
        :: else -> skip
    fi;
    if
        :: search != old_search ->
            printf("search = %e\n", search);
            old_search = search
        :: else -> skip
    fi;
    if
        :: PlanSearch == true ->
            printf("Current state: PlanSearch\n");
        :: else -> skip
    fi;
    if
        :: Deploy == true ->
            printf("Current state: Deploy\n");
        :: else -> skip
    fi;
    if
        :: ActiveSearch == true ->
            printf("Current state: ActiveSearch\n");
        :: else -> skip
    fi;
    if
        :: Return == true ->
            printf("Current state: Return\n");
        :: else -> skip
    fi;
    if
        :: RetrieveBlackBox == true ->
            printf("Current state: RetrieveBlackBox\n");
        :: else -> skip
    fi;
    if
        :: SearchOff == true ->
            printf("Current state: SearchOff\n");
        :: else -> skip
    fi;
}
#define hasToken(place) (place != 0)

inline putToken(place) {
    assert (place != 1)
    place = 1
}

#define consumeToken(place) place = 0


bit Event_17mv5qi = 0
bit Activity_0syv9sd_FROM_Event_17mv5qi = 0
bit Activity_0nwlyl9_FROM_Activity_0syv9sd = 0
bit Event_1poppd1_FROM_Activity_0nwlyl9 = 0
bit Event_1poppd1_FROM_Activity_0ppnjd6 = 0
bit Activity_0pvorq9_FROM_Gateway_0rb75od = 0
bit Activity_0pvorq9_FROM_Event_1aaupcl = 0
bit Activity_0pvorq9_FROM_Event_1poppd1 = 0
bit Gateway_1owfb4m_FROM_Activity_0pvorq9 = 0
bit Activity_04lnckb_FROM_Gateway_1owfb4m = 0
bit Gateway_0rb75od_FROM_Activity_04lnckb = 0
bit Event_00551te_FROM_Gateway_0rb75od = 0
bit Event_00551te_FROM_Activity_1l3bw48 = 0
bit Activity_0zl5lqs_FROM_Activity_0uoxpfd = 0
bit Activity_0zl5lqs_FROM_Event_00551te = 0
bit Activity_1i6huz6_FROM_Activity_0zl5lqs = 0
bit Gateway_0bvrdqi_FROM_Activity_1i6huz6 = 0
bit Event_1a65dx8_FROM_Gateway_0bvrdqi = 0
bit Event_1a65dx8_FROM_Activity_1gpoluy = 0
bit Activity_0pipelz_FROM_Event_1a65dx8 = 0
bit Activity_1hjiquu_FROM_Activity_0pipelz = 0
bit Gateway_0o4xpgj_FROM_Activity_1hjiquu = 0
bit Event_02o56k6_FROM_Gateway_0o4xpgj = 0
bit Activity_0uoxpfd_FROM_Gateway_0o4xpgj = 0
bit Event_1aaupcl_FROM_Gateway_0bvrdqi = 0
bit Event_1aaupcl_FROM_Activity_15xph9w = 0
bit Event_18kspmd_FROM_Gateway_1owfb4m = 0
bit Event_18kspmd_FROM_Activity_10ign21 = 0
bit Activity_0azuxo1_FROM_Event_18kspmd = 0
bit Event_1gibfpo_FROM_Activity_0azuxo1 = 0
bit Event_1bvu1ea = 0
bit Event_1kvb9x7_FROM_Event_1bvu1ea = 0
bit Event_1kvb9x7_FROM_Activity_0nwlyl9 = 0
bit Activity_0ppnjd6_FROM_Event_1kvb9x7 = 0
bit Activity_1bgymg8_FROM_Activity_0ppnjd6 = 0
bit Activity_1bgymg8_FROM_Gateway_0hwogsi = 0
bit Activity_1bgymg8_FROM_Activity_15xph9w = 0
bit Gateway_0hwogsi_FROM_Activity_1bgymg8 = 0
bit Activity_1l3bw48_FROM_Gateway_0hwogsi = 0
bit Event_1i9a79o_FROM_Activity_05h7v9t = 0
bit Event_1i9a79o_FROM_Activity_1l3bw48 = 0
bit Event_1i9a79o_FROM_Activity_1i6huz6 = 0
bit Activity_1egcug9_FROM_Event_1i9a79o = 0
bit Gateway_0ygsp1s_FROM_Activity_1egcug9 = 0
bit Activity_15xph9w_FROM_Gateway_0ygsp1s = 0
bit Activity_1gpoluy_FROM_Gateway_0ygsp1s = 0
bit Event_15hpt57_FROM_Activity_1gpoluy = 0
bit Event_15hpt57_FROM_Activity_1hjiquu = 0
bit Gateway_1s1jaoc_FROM_Event_15hpt57 = 0
bit Activity_1vf2l3e_FROM_Gateway_1s1jaoc = 0
bit Event_09gq76c_FROM_Activity_1vf2l3e = 0
bit Activity_05h7v9t_FROM_Gateway_1s1jaoc = 0
bit Activity_10ign21_FROM_Gateway_0hwogsi = 0
bit Event_04mhz3e_FROM_Activity_10ign21 = 0
inline Event_17mv5qi_BehaviorModel() {
    skip
}

inline Activity_0syv9sd_BehaviorModel() {
    search = on
    conditions = changed
    blackBox = missing
    uuvComms = wait
    risk = assessing
    updateState()
}

inline Activity_0nwlyl9_BehaviorModel() {
    risk = acceptable
    uuvComms = sent
    conditions = same
    updateState()
}

inline Event_1poppd1_BehaviorModel() {
    skip
}

inline Activity_0pvorq9_BehaviorModel() {
    skip
}

inline Activity_04lnckb_BehaviorModel() {
    if
        :: blackBox == missing -> conditions = same
        :: blackBox == missing ->
        conditions = changed;
        risk = assessing;
        uuvComms = wait;
        :: else -> skip
    fi
    updateState()
}

inline Event_00551te_BehaviorModel() {
    skip
}

inline Activity_0zl5lqs_BehaviorModel() {
    if
        :: true ->
        risk = acceptable;
        conditions = same;
        :: true -> risk = notAcceptable
    fi
    uuvComms = sent;
    updateState()
}

inline Activity_1i6huz6_BehaviorModel() {
    if
        :: risk == acceptable -> conditions = same
        :: else -> skip
    fi
    updateState()
}

inline Event_1a65dx8_BehaviorModel() {
    skip
}

inline Activity_0pipelz_BehaviorModel() {
    if
        :: true -> conditions = same
        :: true -> conditions = changed
    fi
    updateState()
}

inline Activity_1hjiquu_BehaviorModel() {
    uuvComms = sent
    updateState()
}

inline Event_02o56k6_BehaviorModel() {
    skip
}

inline Activity_0uoxpfd_BehaviorModel() {
    risk = assessing
    updateState()
}

inline Event_1aaupcl_BehaviorModel() {
    skip
}

inline Event_18kspmd_BehaviorModel() {
    skip
}

inline Activity_0azuxo1_BehaviorModel() {
    search = off
    updateState()
}

inline Event_1gibfpo_BehaviorModel() {
    skip
}

inline Event_1bvu1ea_BehaviorModel() {
    skip
}

inline Event_1kvb9x7_BehaviorModel() {
    skip
}

inline Activity_0ppnjd6_BehaviorModel() {
    uuvComms = waiting
    updateState()
}

inline Activity_1bgymg8_BehaviorModel() {
    if
        :: uuvComms == wait -> blackBox = missing
        :: else ->
        if
            :: true -> blackBox = missing
            :: true -> blackBox = found
        fi
    fi
    updateState()
}

inline Activity_1l3bw48_BehaviorModel() {
    skip
}

inline Event_1i9a79o_BehaviorModel() {
    skip
}

inline Activity_1egcug9_BehaviorModel() {
    uuvComms = waiting
    updateState()
}

inline Activity_15xph9w_BehaviorModel() {
    skip
}

inline Activity_1gpoluy_BehaviorModel() {
    skip
}

inline Event_15hpt57_BehaviorModel() {
    skip
}

inline Activity_1vf2l3e_BehaviorModel() {
    uuvComms = waiting
    updateState()
}

inline Event_09gq76c_BehaviorModel() {
    skip
}

inline Activity_05h7v9t_BehaviorModel() {
    uuvComms = waiting
    updateState()
}

inline Activity_10ign21_BehaviorModel() {
    skip
}

inline Event_04mhz3e_BehaviorModel() {
    skip
}

init {
    run Process_1fc3rc8()
    run Process_1j7puxk()
}

proctype Process_1fc3rc8() {
    d_step {
        printf("ID: Process_1fc3rc8\n")
        stateLogger()
        pid me = _pid
        putToken(Event_17mv5qi)
    }
    do
    :: atomic { ((hasToken(Event_17mv5qi))) ->
        Event_17mv5qi_BehaviorModel()
        d_step {
            printf("ID: Event_17mv5qi\n")
            stateLogger()
            consumeToken(Event_17mv5qi)
            putToken(Activity_0syv9sd_FROM_Event_17mv5qi)
        }
    }
    :: atomic { ((hasToken(Activity_0syv9sd_FROM_Event_17mv5qi))) ->
        Activity_0syv9sd_BehaviorModel()
        d_step {
            printf("ID: Activity_0syv9sd\n")
            stateLogger()
            consumeToken(Activity_0syv9sd_FROM_Event_17mv5qi)
            putToken(Activity_0nwlyl9_FROM_Activity_0syv9sd)
        }
    }
    :: atomic { ((hasToken(Activity_0nwlyl9_FROM_Activity_0syv9sd))) ->
        Activity_0nwlyl9_BehaviorModel()
        d_step {
            printf("ID: Activity_0nwlyl9\n")
            stateLogger()
            consumeToken(Activity_0nwlyl9_FROM_Activity_0syv9sd)
            putToken(Event_1poppd1_FROM_Activity_0nwlyl9)
            putToken(Event_1kvb9x7_FROM_Activity_0nwlyl9)
        }
    }
    :: atomic { ((hasToken(Event_1poppd1_FROM_Activity_0nwlyl9)) && (hasToken(Event_1poppd1_FROM_Activity_0ppnjd6))) ->
        Event_1poppd1_BehaviorModel()
        d_step {
            printf("ID: Event_1poppd1\n")
            stateLogger()
            consumeToken(Event_1poppd1_FROM_Activity_0nwlyl9)
            consumeToken(Event_1poppd1_FROM_Activity_0ppnjd6)
            putToken(Activity_0pvorq9_FROM_Event_1poppd1)
        }
    }
    :: atomic { ((hasToken(Activity_0pvorq9_FROM_Gateway_0rb75od) || hasToken(Activity_0pvorq9_FROM_Event_1aaupcl) || hasToken(Activity_0pvorq9_FROM_Event_1poppd1))) ->
        Activity_0pvorq9_BehaviorModel()
        d_step {
            printf("ID: Activity_0pvorq9\n")
            stateLogger()
            consumeToken(Activity_0pvorq9_FROM_Gateway_0rb75od)
            consumeToken(Activity_0pvorq9_FROM_Event_1aaupcl)
            consumeToken(Activity_0pvorq9_FROM_Event_1poppd1)
            putToken(Gateway_1owfb4m_FROM_Activity_0pvorq9)
        }
    }
    :: atomic { ((hasToken(Gateway_1owfb4m_FROM_Activity_0pvorq9))) ->
        d_step {
            printf("ID: Gateway_1owfb4m\n")
            stateLogger()
            consumeToken(Gateway_1owfb4m_FROM_Activity_0pvorq9)
            if
            :: blackBox == missing -> putToken(Activity_04lnckb_FROM_Gateway_1owfb4m)
            :: blackBox == found -> putToken(Event_18kspmd_FROM_Gateway_1owfb4m)
            :: atomic{else -> assert false}
            fi
        }
    }
    :: atomic { ((hasToken(Activity_04lnckb_FROM_Gateway_1owfb4m))) ->
        Activity_04lnckb_BehaviorModel()
        d_step {
            printf("ID: Activity_04lnckb\n")
            stateLogger()
            consumeToken(Activity_04lnckb_FROM_Gateway_1owfb4m)
            putToken(Gateway_0rb75od_FROM_Activity_04lnckb)
        }
    }
    :: atomic { ((hasToken(Gateway_0rb75od_FROM_Activity_04lnckb))) ->
        d_step {
            printf("ID: Gateway_0rb75od\n")
            stateLogger()
            consumeToken(Gateway_0rb75od_FROM_Activity_04lnckb)
            if
            :: conditions == changed && blackBox == missing -> putToken(Event_00551te_FROM_Gateway_0rb75od)
            :: conditions == same || blackBox == found -> putToken(Activity_0pvorq9_FROM_Gateway_0rb75od)
            :: atomic{else -> assert false}
            fi
        }
    }
    :: atomic { ((hasToken(Event_00551te_FROM_Gateway_0rb75od)) && (hasToken(Event_00551te_FROM_Activity_1l3bw48))) ->
        Event_00551te_BehaviorModel()
        d_step {
            printf("ID: Event_00551te\n")
            stateLogger()
            consumeToken(Event_00551te_FROM_Gateway_0rb75od)
            consumeToken(Event_00551te_FROM_Activity_1l3bw48)
            putToken(Activity_0zl5lqs_FROM_Event_00551te)
        }
    }
    :: atomic { ((hasToken(Activity_0zl5lqs_FROM_Activity_0uoxpfd) || hasToken(Activity_0zl5lqs_FROM_Event_00551te))) ->
        Activity_0zl5lqs_BehaviorModel()
        d_step {
            printf("ID: Activity_0zl5lqs\n")
            stateLogger()
            consumeToken(Activity_0zl5lqs_FROM_Activity_0uoxpfd)
            consumeToken(Activity_0zl5lqs_FROM_Event_00551te)
            putToken(Activity_1i6huz6_FROM_Activity_0zl5lqs)
        }
    }
    :: atomic { ((hasToken(Activity_1i6huz6_FROM_Activity_0zl5lqs))) ->
        Activity_1i6huz6_BehaviorModel()
        d_step {
            printf("ID: Activity_1i6huz6\n")
            stateLogger()
            consumeToken(Activity_1i6huz6_FROM_Activity_0zl5lqs)
            putToken(Gateway_0bvrdqi_FROM_Activity_1i6huz6)
            putToken(Event_1i9a79o_FROM_Activity_1i6huz6)
        }
    }
    :: atomic { ((hasToken(Gateway_0bvrdqi_FROM_Activity_1i6huz6))) ->
        d_step {
            printf("ID: Gateway_0bvrdqi\n")
            stateLogger()
            consumeToken(Gateway_0bvrdqi_FROM_Activity_1i6huz6)
            if
            :: risk == notAcceptable -> putToken(Event_1a65dx8_FROM_Gateway_0bvrdqi)
            :: risk == acceptable -> putToken(Event_1aaupcl_FROM_Gateway_0bvrdqi)
            :: atomic{else -> assert false}
            fi
        }
    }
    :: atomic { ((hasToken(Event_1a65dx8_FROM_Gateway_0bvrdqi)) && (hasToken(Event_1a65dx8_FROM_Activity_1gpoluy))) ->
        Event_1a65dx8_BehaviorModel()
        d_step {
            printf("ID: Event_1a65dx8\n")
            stateLogger()
            consumeToken(Event_1a65dx8_FROM_Gateway_0bvrdqi)
            consumeToken(Event_1a65dx8_FROM_Activity_1gpoluy)
            putToken(Activity_0pipelz_FROM_Event_1a65dx8)
        }
    }
    :: atomic { ((hasToken(Activity_0pipelz_FROM_Event_1a65dx8))) ->
        Activity_0pipelz_BehaviorModel()
        d_step {
            printf("ID: Activity_0pipelz\n")
            stateLogger()
            consumeToken(Activity_0pipelz_FROM_Event_1a65dx8)
            putToken(Activity_1hjiquu_FROM_Activity_0pipelz)
        }
    }
    :: atomic { ((hasToken(Activity_1hjiquu_FROM_Activity_0pipelz))) ->
        Activity_1hjiquu_BehaviorModel()
        d_step {
            printf("ID: Activity_1hjiquu\n")
            stateLogger()
            consumeToken(Activity_1hjiquu_FROM_Activity_0pipelz)
            putToken(Gateway_0o4xpgj_FROM_Activity_1hjiquu)
            putToken(Event_15hpt57_FROM_Activity_1hjiquu)
        }
    }
    :: atomic { ((hasToken(Gateway_0o4xpgj_FROM_Activity_1hjiquu))) ->
        d_step {
            printf("ID: Gateway_0o4xpgj\n")
            stateLogger()
            consumeToken(Gateway_0o4xpgj_FROM_Activity_1hjiquu)
            if
            :: conditions == same -> putToken(Event_02o56k6_FROM_Gateway_0o4xpgj)
            :: conditions == changed -> putToken(Activity_0uoxpfd_FROM_Gateway_0o4xpgj)
            :: atomic{else -> assert false}
            fi
        }
    }
    :: atomic { ((hasToken(Event_02o56k6_FROM_Gateway_0o4xpgj))) ->
        Event_02o56k6_BehaviorModel()
        d_step {
            printf("ID: Event_02o56k6\n")
            stateLogger()
            consumeToken(Event_02o56k6_FROM_Gateway_0o4xpgj)
        }
        break
    }
    :: atomic { ((hasToken(Activity_0uoxpfd_FROM_Gateway_0o4xpgj))) ->
        Activity_0uoxpfd_BehaviorModel()
        d_step {
            printf("ID: Activity_0uoxpfd\n")
            stateLogger()
            consumeToken(Activity_0uoxpfd_FROM_Gateway_0o4xpgj)
            putToken(Activity_0zl5lqs_FROM_Activity_0uoxpfd)
        }
    }
    :: atomic { ((hasToken(Event_1aaupcl_FROM_Gateway_0bvrdqi)) && (hasToken(Event_1aaupcl_FROM_Activity_15xph9w))) ->
        Event_1aaupcl_BehaviorModel()
        d_step {
            printf("ID: Event_1aaupcl\n")
            stateLogger()
            consumeToken(Event_1aaupcl_FROM_Gateway_0bvrdqi)
            consumeToken(Event_1aaupcl_FROM_Activity_15xph9w)
            putToken(Activity_0pvorq9_FROM_Event_1aaupcl)
        }
    }
    :: atomic { ((hasToken(Event_18kspmd_FROM_Gateway_1owfb4m)) && (hasToken(Event_18kspmd_FROM_Activity_10ign21))) ->
        Event_18kspmd_BehaviorModel()
        d_step {
            printf("ID: Event_18kspmd\n")
            stateLogger()
            consumeToken(Event_18kspmd_FROM_Gateway_1owfb4m)
            consumeToken(Event_18kspmd_FROM_Activity_10ign21)
            putToken(Activity_0azuxo1_FROM_Event_18kspmd)
        }
    }
    :: atomic { ((hasToken(Activity_0azuxo1_FROM_Event_18kspmd))) ->
        Activity_0azuxo1_BehaviorModel()
        d_step {
            printf("ID: Activity_0azuxo1\n")
            stateLogger()
            consumeToken(Activity_0azuxo1_FROM_Event_18kspmd)
            putToken(Event_1gibfpo_FROM_Activity_0azuxo1)
        }
    }
    :: atomic { ((hasToken(Event_1gibfpo_FROM_Activity_0azuxo1))) ->
        Event_1gibfpo_BehaviorModel()
        d_step {
            printf("ID: Event_1gibfpo\n")
            stateLogger()
            consumeToken(Event_1gibfpo_FROM_Activity_0azuxo1)
        }
        break
    }
    od
}
proctype Process_1j7puxk() {
    d_step {
        printf("ID: Process_1j7puxk\n")
        stateLogger()
        pid me = _pid
        putToken(Event_1bvu1ea)
    }
    do
    :: atomic { ((hasToken(Event_1bvu1ea))) ->
        Event_1bvu1ea_BehaviorModel()
        d_step {
            printf("ID: Event_1bvu1ea\n")
            stateLogger()
            consumeToken(Event_1bvu1ea)
            putToken(Event_1kvb9x7_FROM_Event_1bvu1ea)
        }
    }
    :: atomic { ((hasToken(Event_1kvb9x7_FROM_Event_1bvu1ea)) && (hasToken(Event_1kvb9x7_FROM_Activity_0nwlyl9))) ->
        Event_1kvb9x7_BehaviorModel()
        d_step {
            printf("ID: Event_1kvb9x7\n")
            stateLogger()
            consumeToken(Event_1kvb9x7_FROM_Event_1bvu1ea)
            consumeToken(Event_1kvb9x7_FROM_Activity_0nwlyl9)
            putToken(Activity_0ppnjd6_FROM_Event_1kvb9x7)
        }
    }
    :: atomic { ((hasToken(Activity_0ppnjd6_FROM_Event_1kvb9x7))) ->
        Activity_0ppnjd6_BehaviorModel()
        d_step {
            printf("ID: Activity_0ppnjd6\n")
            stateLogger()
            consumeToken(Activity_0ppnjd6_FROM_Event_1kvb9x7)
            putToken(Activity_1bgymg8_FROM_Activity_0ppnjd6)
            putToken(Event_1poppd1_FROM_Activity_0ppnjd6)
        }
    }
    :: atomic { ((hasToken(Activity_1bgymg8_FROM_Activity_0ppnjd6) || hasToken(Activity_1bgymg8_FROM_Gateway_0hwogsi) || hasToken(Activity_1bgymg8_FROM_Activity_15xph9w))) ->
        Activity_1bgymg8_BehaviorModel()
        d_step {
            printf("ID: Activity_1bgymg8\n")
            stateLogger()
            consumeToken(Activity_1bgymg8_FROM_Activity_0ppnjd6)
            consumeToken(Activity_1bgymg8_FROM_Gateway_0hwogsi)
            consumeToken(Activity_1bgymg8_FROM_Activity_15xph9w)
            putToken(Gateway_0hwogsi_FROM_Activity_1bgymg8)
        }
    }
    :: atomic { ((hasToken(Gateway_0hwogsi_FROM_Activity_1bgymg8))) ->
        d_step {
            printf("ID: Gateway_0hwogsi\n")
            stateLogger()
            consumeToken(Gateway_0hwogsi_FROM_Activity_1bgymg8)
            if
            :: uuvComms != waiting && blackBox == missing -> putToken(Activity_1l3bw48_FROM_Gateway_0hwogsi)
            :: blackBox == found -> putToken(Activity_10ign21_FROM_Gateway_0hwogsi)
            :: uuvComms == waiting && blackBox == missing -> putToken(Activity_1bgymg8_FROM_Gateway_0hwogsi)
            :: atomic{else -> assert false}
            fi
        }
    }
    :: atomic { ((hasToken(Activity_1l3bw48_FROM_Gateway_0hwogsi))) ->
        Activity_1l3bw48_BehaviorModel()
        d_step {
            printf("ID: Activity_1l3bw48\n")
            stateLogger()
            consumeToken(Activity_1l3bw48_FROM_Gateway_0hwogsi)
            putToken(Event_1i9a79o_FROM_Activity_1l3bw48)
            putToken(Event_00551te_FROM_Activity_1l3bw48)
        }
    }
    :: atomic { ((hasToken(Event_1i9a79o_FROM_Activity_05h7v9t) || hasToken(Event_1i9a79o_FROM_Activity_1l3bw48)) && (hasToken(Event_1i9a79o_FROM_Activity_1i6huz6))) ->
        Event_1i9a79o_BehaviorModel()
        d_step {
            printf("ID: Event_1i9a79o\n")
            stateLogger()
            consumeToken(Event_1i9a79o_FROM_Activity_05h7v9t)
            consumeToken(Event_1i9a79o_FROM_Activity_1l3bw48)
            consumeToken(Event_1i9a79o_FROM_Activity_1i6huz6)
            putToken(Activity_1egcug9_FROM_Event_1i9a79o)
        }
    }
    :: atomic { ((hasToken(Activity_1egcug9_FROM_Event_1i9a79o))) ->
        Activity_1egcug9_BehaviorModel()
        d_step {
            printf("ID: Activity_1egcug9\n")
            stateLogger()
            consumeToken(Activity_1egcug9_FROM_Event_1i9a79o)
            putToken(Gateway_0ygsp1s_FROM_Activity_1egcug9)
        }
    }
    :: atomic { ((hasToken(Gateway_0ygsp1s_FROM_Activity_1egcug9))) ->
        d_step {
            printf("ID: Gateway_0ygsp1s\n")
            stateLogger()
            consumeToken(Gateway_0ygsp1s_FROM_Activity_1egcug9)
            if
            :: search == on && risk == acceptable -> putToken(Activity_15xph9w_FROM_Gateway_0ygsp1s)
            :: search == on && risk == notAcceptable -> putToken(Activity_1gpoluy_FROM_Gateway_0ygsp1s)
            :: atomic{else -> assert false}
            fi
        }
    }
    :: atomic { ((hasToken(Activity_15xph9w_FROM_Gateway_0ygsp1s))) ->
        Activity_15xph9w_BehaviorModel()
        d_step {
            printf("ID: Activity_15xph9w\n")
            stateLogger()
            consumeToken(Activity_15xph9w_FROM_Gateway_0ygsp1s)
            putToken(Activity_1bgymg8_FROM_Activity_15xph9w)
            putToken(Event_1aaupcl_FROM_Activity_15xph9w)
        }
    }
    :: atomic { ((hasToken(Activity_1gpoluy_FROM_Gateway_0ygsp1s))) ->
        Activity_1gpoluy_BehaviorModel()
        d_step {
            printf("ID: Activity_1gpoluy\n")
            stateLogger()
            consumeToken(Activity_1gpoluy_FROM_Gateway_0ygsp1s)
            putToken(Event_15hpt57_FROM_Activity_1gpoluy)
            putToken(Event_1a65dx8_FROM_Activity_1gpoluy)
        }
    }
    :: atomic { ((hasToken(Event_15hpt57_FROM_Activity_1gpoluy)) && (hasToken(Event_15hpt57_FROM_Activity_1hjiquu))) ->
        Event_15hpt57_BehaviorModel()
        d_step {
            printf("ID: Event_15hpt57\n")
            stateLogger()
            consumeToken(Event_15hpt57_FROM_Activity_1gpoluy)
            consumeToken(Event_15hpt57_FROM_Activity_1hjiquu)
            putToken(Gateway_1s1jaoc_FROM_Event_15hpt57)
        }
    }
    :: atomic { ((hasToken(Gateway_1s1jaoc_FROM_Event_15hpt57))) ->
        d_step {
            printf("ID: Gateway_1s1jaoc\n")
            stateLogger()
            consumeToken(Gateway_1s1jaoc_FROM_Event_15hpt57)
            if
            :: risk == notAcceptable && conditions == same -> putToken(Activity_1vf2l3e_FROM_Gateway_1s1jaoc)
            :: risk == acceptable || conditions == changed -> putToken(Activity_05h7v9t_FROM_Gateway_1s1jaoc)
            :: atomic{else -> assert false}
            fi
        }
    }
    :: atomic { ((hasToken(Activity_1vf2l3e_FROM_Gateway_1s1jaoc))) ->
        Activity_1vf2l3e_BehaviorModel()
        d_step {
            printf("ID: Activity_1vf2l3e\n")
            stateLogger()
            consumeToken(Activity_1vf2l3e_FROM_Gateway_1s1jaoc)
            putToken(Event_09gq76c_FROM_Activity_1vf2l3e)
        }
    }
    :: atomic { ((hasToken(Event_09gq76c_FROM_Activity_1vf2l3e))) ->
        Event_09gq76c_BehaviorModel()
        d_step {
            printf("ID: Event_09gq76c\n")
            stateLogger()
            consumeToken(Event_09gq76c_FROM_Activity_1vf2l3e)
        }
        break
    }
    :: atomic { ((hasToken(Activity_05h7v9t_FROM_Gateway_1s1jaoc))) ->
        Activity_05h7v9t_BehaviorModel()
        d_step {
            printf("ID: Activity_05h7v9t\n")
            stateLogger()
            consumeToken(Activity_05h7v9t_FROM_Gateway_1s1jaoc)
            putToken(Event_1i9a79o_FROM_Activity_05h7v9t)
        }
    }
    :: atomic { ((hasToken(Activity_10ign21_FROM_Gateway_0hwogsi))) ->
        Activity_10ign21_BehaviorModel()
        d_step {
            printf("ID: Activity_10ign21\n")
            stateLogger()
            consumeToken(Activity_10ign21_FROM_Gateway_0hwogsi)
            putToken(Event_04mhz3e_FROM_Activity_10ign21)
            putToken(Event_18kspmd_FROM_Activity_10ign21)
        }
    }
    :: atomic { ((hasToken(Event_04mhz3e_FROM_Activity_10ign21))) ->
        Event_04mhz3e_BehaviorModel()
        d_step {
            printf("ID: Event_04mhz3e\n")
            stateLogger()
            consumeToken(Event_04mhz3e_FROM_Activity_10ign21)
        }
        break
    }
    od
}
