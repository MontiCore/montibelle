private import VerificationLibrary::untimed;

#untimed part def Untimed_Scheduler_LLR 
    specializes Untimed_Scheduler_HLR3, Untimed_Scheduler_HLR2
{
  redefines queue: Untimed_Queue_LLR;
  redefines limiter: Untimed_RateLimiter_LLR { 
    redefines limiter.cap = capacity;
  }

  connect input to queue.input;
  connect queue.output to limiter.input;
  connect limiter.control to queue.control;
  connect limiter.output to output;
}