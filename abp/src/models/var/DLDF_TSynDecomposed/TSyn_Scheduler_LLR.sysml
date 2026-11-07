private import VerificationLibrary::tsyn;

#tsyn part def TSyn_Scheduler_LLR 
    specializes TSyn_Scheduler_HLR3, Scheduler_HLR2
{
  port input: ~Packets redefines TSyn_Scheduler_HLR3::input, Scheduler_HLR2::input;
  port output: Packets redefines TSyn_Scheduler_HLR3::output, Scheduler_HLR2::output;
  redefines queue: TSyn_Queue_LLR;
  redefines limiter: TSyn_RateLimiter_LLR { 
    redefines limiter.cap = capacity;
  }

  connect input to queue.input;
  connect queue.output to limiter.input;
  connect limiter.control to queue.control;
  connect limiter.output to output;
}