part def Scheduler_LLR specializes Scheduler_HLR3, Scheduler_HLR2 {
  redefines queue: Queue_LLR;
  redefines limiter: RateLimiter_LLR { 
    redefines limiter.cap = capacity;
  }

  connect input to queue.input;
  connect queue.output to limiter.input;
  connect limiter.control to queue.control;
  connect limiter.output to output;
}