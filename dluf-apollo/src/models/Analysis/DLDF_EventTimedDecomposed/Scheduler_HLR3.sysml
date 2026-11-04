part def Scheduler_HLR3 specializes Scheduler_HLR2 {
  part queue: Queue_HLR3;
  part limiter: RateLimiter_HLR3 { redefines cap = capacity; }

  connect input to queue.input;
  connect queue.output to limiter.input;
  connect limiter.control to queue.control;
  connect limiter.output to output;
}