# ICT3101_Frama_C_Lab

"Smoke Tests" 
- can be used to detect that some preconditions are unsatisfiable.
frama-c-gui -wp -wp-smoke-tests file.c

"Bullet Indicators"

- red, orange [on precondition of function] - exists a reachable call to this function the precondition will be necessarily violated
- red [in list of goals] - prover succeeded in proving that the precondition is inconsistent


## Contract
- \valid_read  <-- used when pointer needs to be read
- \valid       <-- used when pointer will be assigned with another value
- \old          <-- 
- \assigns      <-- 
- \separated    <-- 
