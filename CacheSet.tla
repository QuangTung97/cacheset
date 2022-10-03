------ MODULE CacheSet ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node

MaxValue == 5

VersionRange == 1..(MaxValue + 2)

VARIABLES pc,
    db_version, db_value, log,
    next_lease, cache_version, cache_version_lease, cache_values,
    local_version, local_value, local_lease,
    consume_seq


db_vars == <<db_version, db_value, log>>
cache_vars == <<next_lease, cache_version, cache_version_lease, cache_values>>
local_vars == <<pc, local_version, local_value, local_lease>>

LogEntry == [type: {"Version", "Value"}, key: Nat]

TypeOK ==
    /\ pc \in [Node -> {"Init", "GetDBVersion", "SetCacheVersion", "Terminated"}]

    /\ db_version \in Nat
    /\ db_value \in Nat
    /\ log \in Seq(LogEntry)

    /\ next_lease \in Nat
    /\ cache_version \in Nat
    /\ cache_version_lease \in Nat
    /\ cache_values \in [VersionRange -> Nat]

    /\ local_version \in [Node -> Nat]
    /\ local_value \in [Node -> Nat]
    /\ local_lease \in [Node -> Nat]

    /\ consume_seq \in Nat


Init ==
    /\ pc = [n \in Node |-> "Init"]

    /\ db_version = 1
    /\ db_value = 0
    /\ log = <<>>

    /\ next_lease = 0
    /\ cache_version = 0
    /\ cache_version_lease = 0
    /\ cache_values = [v \in VersionRange |-> 0]
    
    /\ local_version = [n \in Node |-> 0]
    /\ local_value = [n \in Node |-> 0]
    /\ local_lease = [n \in Node |-> 0]

    /\ consume_seq = 0


logEntry(t, k) ==
    [type |-> t, key |-> k]


UpdateDBValue ==
    /\ db_value < MaxValue
    /\ db_value' = db_value + 1
    /\ log' = Append(log, logEntry("Value", db_version))
    /\ UNCHANGED db_version
    /\ UNCHANGED <<cache_vars, local_vars, consume_seq>>


UpdateDBValueAndVersion ==
    /\ db_value < MaxValue
    /\ db_value' = db_value + 1
    /\ db_version' = db_version + 1
    /\ log' = Append(Append(log, logEntry("Version", 0)), logEntry("Value", db_version))
    /\ UNCHANGED <<cache_vars, local_vars, consume_seq>>


goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


GetCacheVersion(n) ==
    /\ pc[n] = "Init"
    /\ local_version' = [local_version EXCEPT ![n] = cache_version]
    /\ IF local_version'[n] = 0
        THEN
            /\ next_lease' = next_lease + 1
            /\ cache_version_lease' = next_lease'
            /\ local_lease' = [local_lease EXCEPT ![n] = cache_version_lease']
            /\ goto(n, "GetDBVersion")
            /\ UNCHANGED <<cache_version, cache_values>>
        ELSE
            /\ goto(n, "Terminated")
            /\ UNCHANGED <<local_lease, cache_vars>>
    /\ UNCHANGED <<local_value, db_vars, consume_seq>>


GetDBVersion(n) ==
    /\ pc[n] = "GetDBVersion"
    /\ goto(n, "SetCacheVersion")
    /\ local_version' = [local_version EXCEPT ![n] = db_version]
    /\ UNCHANGED <<db_vars, cache_vars, local_value, local_lease, consume_seq>>


SetCacheVersion(n) ==
    /\ pc[n] = "SetCacheVersion"
    /\ goto(n, "Terminated")
    /\ IF cache_version_lease = local_lease[n]
        THEN
            /\ cache_version' = local_version[n]
            /\ cache_version_lease' = 0
        ELSE
            /\ UNCHANGED <<cache_version, cache_version_lease>>
    /\ UNCHANGED <<db_vars, local_version, local_value, local_lease,
        cache_values, next_lease, consume_seq>>


Consume ==
    /\ consume_seq < Len(log)
    /\ consume_seq' = consume_seq + 1
    /\ LET e == log[consume_seq'] IN
        /\ IF e.type = "Version"
            THEN
                /\ cache_version' = 0
                /\ cache_version_lease' = 0
                /\ UNCHANGED <<cache_values, next_lease>>
            ELSE
                /\ cache_values' = [cache_values EXCEPT ![e.key] = 0]
                /\ UNCHANGED <<cache_version, cache_version_lease, next_lease>>
    /\ UNCHANGED <<db_vars, local_vars>>


TerminatedCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ consume_seq = Len(log)


Terminated ==
    /\ TerminatedCond
    /\ UNCHANGED <<db_vars, cache_vars, local_vars, consume_seq>>


Inv ==
    /\ TerminatedCond =>
        \/ cache_version = 0
        \/ cache_version = db_version


Next ==
    \/ UpdateDBValue
    \/ UpdateDBValueAndVersion
    \/ \E n \in Node:
        \/ GetCacheVersion(n)
        \/ GetDBVersion(n)
        \/ SetCacheVersion(n)
    \/ Consume
    \/ Terminated


Symmetry == Permutations(Node)

MaxValueConstraint == db_value <= MaxValue

====