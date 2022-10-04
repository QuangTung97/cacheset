------ MODULE CacheSet ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node

MaxValue == 3

VersionRange == 1..(MaxValue + 2)

VARIABLES pc,
    db_version, db_value, log,
    next_lease,
    cache_version, cache_version_lease,
    cache_values, cache_values_lease, cache_values_origin,
    local_version, local_value, local_lease, local_origin,
    consume_seq


db_vars == <<db_version, db_value, log>>
cache_vars == <<next_lease, cache_version, cache_version_lease,
    cache_values, cache_values_lease, cache_values_origin>>
local_vars == <<pc, local_version, local_value, local_lease, local_origin>>

LogEntry == [type: {"Version", "Value"}, key: Nat]

TypeOK ==
    /\ pc \in [Node -> {
        "Init", "GetDBVersion", "SetCacheVersion",
        "GetCacheValue", "GetLowerCacheValue", "GetDBValue", "SetCacheValue",
        "Terminated"}]

    /\ db_version \in Nat
    /\ db_value \in Nat
    /\ log \in Seq(LogEntry)

    /\ next_lease \in Nat
    /\ cache_version \in Nat
    /\ cache_version_lease \in Nat
    /\ cache_values \in [VersionRange -> Nat]
    /\ cache_values_lease \in [VersionRange -> Nat]
    /\ cache_values_origin \in [VersionRange -> Nat]

    /\ local_version \in [Node -> Nat]
    /\ local_value \in [Node -> Nat]
    /\ local_lease \in [Node -> Nat]
    /\ local_origin \in [Node -> Nat]

    /\ consume_seq \in Nat


Init ==
    /\ pc = [n \in Node |-> "Init"]

    /\ db_version = 1
    /\ db_value = 1
    /\ log = <<>>

    /\ next_lease = 0
    /\ cache_version = 0
    /\ cache_version_lease = 0
    /\ cache_values = [v \in VersionRange |-> 0]
    /\ cache_values_lease = [v \in VersionRange |-> 0]
    /\ cache_values_origin = [v \in VersionRange |-> 0]
    
    /\ local_version = [n \in Node |-> 0]
    /\ local_value = [n \in Node |-> 0]
    /\ local_lease = [n \in Node |-> 0]
    /\ local_origin = [n \in Node |-> 0]

    /\ consume_seq = 0


logEntry(t, k) ==
    [type |-> t, key |-> k]


UpdateDBValue ==
    /\ db_value < MaxValue
    /\ db_value' = db_value + 1
    /\ IF db_version > 1
        THEN
            LET
                log1 == Append(log, logEntry("Value", db_version - 1))
            IN log' = Append(log1, logEntry("Value", db_version))
        ELSE
            log' = Append(log, logEntry("Value", db_version))
    /\ UNCHANGED db_version
    /\ UNCHANGED <<cache_vars, local_vars, consume_seq>>


UpdateDBValueAndVersion ==
    /\ db_value < MaxValue
    /\ db_value' = db_value + 1
    /\ db_version' = db_version + 1
    /\ IF db_version' > 1
        THEN
            LET
                log1 == Append(log, logEntry("Version", 0))
                log2 == Append(log1, logEntry("Value", db_version' - 1))
            IN log' = Append(log2, logEntry("Value", db_version'))
        ELSE
            LET
                log1 == Append(log, logEntry("Version", 0))
            IN
            log' = Append(log1, logEntry("Value", db_version'))
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
            /\ UNCHANGED <<cache_version, cache_values,
                cache_values_lease, cache_values_origin>>
        ELSE
            /\ goto(n, "GetCacheValue")
            /\ UNCHANGED <<local_lease, cache_vars>>
    /\ UNCHANGED <<local_value, local_origin, db_vars, consume_seq>>


GetDBVersion(n) ==
    /\ pc[n] = "GetDBVersion"
    /\ goto(n, "SetCacheVersion")
    /\ local_version' = [local_version EXCEPT ![n] = db_version]
    /\ UNCHANGED <<db_vars, cache_vars, local_value, local_origin,
        local_lease, consume_seq>>


SetCacheVersion(n) ==
    /\ pc[n] = "SetCacheVersion"
    /\ goto(n, "GetCacheValue")
    /\ IF cache_version_lease = local_lease[n]
        THEN
            /\ cache_version' = local_version[n]
            /\ cache_version_lease' = 0
        ELSE
            /\ UNCHANGED <<cache_version, cache_version_lease>>
    /\ UNCHANGED <<db_vars, local_version, local_value, local_origin, local_lease,
        cache_values, cache_values_lease, cache_values_origin,
        next_lease, consume_seq>>


GetCacheValue(n) ==
    /\ pc[n] = "GetCacheValue"
    /\ local_value' = [local_value EXCEPT ![n] = cache_values[local_version[n]]]
    /\ IF local_value'[n] = 0
        THEN
            /\ next_lease' = next_lease + 1
            /\ cache_values_lease' = [
                cache_values_lease EXCEPT ![local_version[n]] = next_lease']
            /\ local_lease' = [local_lease EXCEPT ![n] = next_lease']
            /\ IF local_version[n] = 1
                THEN goto(n, "GetDBValue")
                ELSE goto(n, "GetLowerCacheValue")
        ELSE
            /\ goto(n, "Terminated")
            /\ UNCHANGED <<local_lease, cache_values_lease, next_lease>>
    /\ UNCHANGED <<local_version, local_origin>>
    /\ UNCHANGED <<cache_version, cache_version_lease,
        cache_values, cache_values_origin>>
    /\ UNCHANGED <<db_vars, consume_seq>>


GetLowerCacheValue(n) ==
    /\ pc[n] = "GetLowerCacheValue"
    /\ local_value' = [local_value EXCEPT ![n] = cache_values[local_version[n] - 1]]
    /\ local_origin' = [local_origin
            EXCEPT ![n] = cache_values_origin[local_version[n] - 1]]
    /\ IF local_value'[n] = 0 \/ local_origin'[n] + 1 < local_version[n]
        THEN
            /\ goto(n, "GetDBValue")
        ELSE
            /\ goto(n, "SetCacheValue")
    /\ UNCHANGED <<local_lease, local_version>>
    /\ UNCHANGED <<cache_vars, db_vars, consume_seq>>


GetDBValue(n) ==
    /\ pc[n] = "GetDBValue"
    /\ local_value' = [local_value EXCEPT ![n] = db_value]
    /\ local_origin' = [local_origin EXCEPT ![n] = local_version[n]]
    /\ goto(n, "SetCacheValue")
    /\ UNCHANGED <<local_lease, local_version>>
    /\ UNCHANGED <<cache_vars, db_vars, consume_seq>>


SetCacheValue(n) ==
    /\ pc[n] = "SetCacheValue"
    /\ goto(n, "Terminated")
    /\ IF cache_values_lease[local_version[n]] = local_lease[n]
        THEN
            /\ cache_values' = [cache_values EXCEPT ![local_version[n]] = local_value[n]]
            /\ cache_values_lease' = [cache_values_lease EXCEPT ![local_version[n]] = 0]
            /\ cache_values_origin' = [cache_values_origin EXCEPT ![local_version[n]] = local_origin[n]]
        ELSE
            /\ UNCHANGED <<cache_values, cache_values_lease, cache_values_origin>>
    /\ UNCHANGED <<cache_version, cache_version_lease, next_lease>>
    /\ UNCHANGED <<local_lease, local_version, local_value, local_origin>>
    /\ UNCHANGED <<db_vars, consume_seq>>
    


Consume ==
    /\ consume_seq < Len(log)
    /\ consume_seq' = consume_seq + 1
    /\ LET e == log[consume_seq'] IN
        /\ IF e.type = "Version"
            THEN
                /\ cache_version' = 0
                /\ cache_version_lease' = 0
                /\ UNCHANGED <<cache_values,
                    cache_values_lease, cache_values_origin, next_lease>>
            ELSE
                /\ cache_values' = [cache_values EXCEPT ![e.key] = 0]
                /\ cache_values_lease' = [cache_values_lease EXCEPT ![e.key] = 0]
                /\ cache_values_origin' = [cache_values_origin EXCEPT ![e.key] = 0]
                /\ UNCHANGED <<cache_version, cache_version_lease, next_lease>>
    /\ UNCHANGED <<db_vars, local_vars>>


TerminatedCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ consume_seq = Len(log)


Terminated ==
    /\ TerminatedCond
    /\ UNCHANGED <<db_vars, cache_vars, local_vars, consume_seq>>


VersionConsistency ==
    \/ cache_version = 0
    \/ cache_version = db_version

ValueConsistency ==
    \/ cache_values[db_version] = 0
    \/ cache_values[db_version] = db_value

Inv ==
    /\ TerminatedCond => VersionConsistency /\ ValueConsistency


Next ==
    \/ UpdateDBValue
    \/ UpdateDBValueAndVersion
    \/ \E n \in Node:
        \/ GetCacheVersion(n)
        \/ GetDBVersion(n)
        \/ SetCacheVersion(n)
        \/ GetCacheValue(n)
        \/ GetLowerCacheValue(n)
        \/ GetDBValue(n)
        \/ SetCacheValue(n)
    \/ Consume
    \/ Terminated


Symmetry == Permutations(Node)

MaxValueConstraint == db_value <= MaxValue

====