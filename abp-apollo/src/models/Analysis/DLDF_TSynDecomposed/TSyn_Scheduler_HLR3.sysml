private import VerificationLibrary::tsyn;

#tsyn part def TSyn_Scheduler_HLR3 specializes TSyn_Scheduler_HLR2 {
  part queue: TSyn_Queue_HLR3;
  part limiter: TSyn_RateLimiter_HLR3 { redefines cap = capacity; }

  connect input to queue.input;
  connect queue.output to limiter.input;
  connect limiter.control to queue.control;
  connect limiter.output to output;
}