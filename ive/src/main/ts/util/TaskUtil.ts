import { getLogger } from "log4js";
import { ProcessExecution, Task, TaskExecution, TaskProcessEndEvent, TaskProcessStartEvent, tasks, TaskScope } from "vscode";

export class TaskUtil {

  public static async execute(name: string, command: ProcessExecution) : Promise<TaskExecution> {
    return new Promise(async (resolve, reject) =>
    {
      let execution: TaskExecution;
      try {
        execution = await tasks.executeTask(new Task(
          { type: name },
          TaskScope.Workspace,
          name,
          "Ive",
          command
        ));
      }
      catch(executionError) {
        let reason = `The underlying system does not support process executions`;
        getLogger().fatal(`Task execution failed. ${reason}.`, executionError);
        return reject(reason);
      }
      return resolve(execution);
    });
  }

  public static async onExecutionEndOf(execution: TaskExecution) : Promise<TaskProcessEndEvent> {
    getLogger().trace(`Listening for termination of "${execution.task.name}"`);

    return new Promise((resolve, _) =>
    {
      let disposableEvent = tasks.onDidEndTaskProcess(e =>
      {
        if(e.execution === execution) {
          getLogger().trace(`Detected the termination of  "${execution.task.name}"`);
          setTimeout(disposableEvent.dispose, 1000);
          return resolve(e);
        }
      });
    });
  }

  public static async onExecutionStartOf(execution: TaskExecution) : Promise<TaskProcessStartEvent> {
    getLogger().trace(`Listening for start of       "${execution.task.name}"`);

    return new Promise((resolve, _) =>
    {
      let disposableEvent = tasks.onDidStartTaskProcess(e =>
      {
        if(e.execution === execution) {
          getLogger().trace(`Detected the start of        "${execution.task.name}"`);
          setTimeout(disposableEvent.dispose, 1000);
          return resolve(e);
        }
      });
    });
  }

}