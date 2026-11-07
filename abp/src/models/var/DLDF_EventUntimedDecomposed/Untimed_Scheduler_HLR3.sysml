private import VerificationLibrary::untimed;

#untimed part def Untimed_Scheduler_HLR3 
    specializes Untimed_Scheduler_HLR2
{
  part queue: Untimed_Queue_HLR3;
  part limiter: Untimed_RateLimiter_HLR3 { redefines cap = capacity; }

  connect input to queue.input;
  connect queue.output to limiter.input;
  connect limiter.control to queue.control;
  connect limiter.output to output;
}