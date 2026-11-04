import logging
import random
import string

from flask import logging as flog


def init_log(app):
  global log
  gunicorn_error_logger = logging.getLogger("gunicorn.error")

  if gunicorn_error_logger.handlers:
    app.logger.handlers = gunicorn_error_logger.handlers
  else:
    if flog.default_handler not in app.logger.handlers:
      app.logger.addHandler(flog.default_handler)
    flog.default_handler.setLevel(logging.DEBUG)

  app.logger.setLevel(logging.DEBUG)
  app.logger.propagate = False
  app.app_context().push()

  flog.default_handler.setFormatter(
    logging.Formatter(
      fmt="[%(asctime)s] [%(levelname)s] %(message)s",
      datefmt="%d/%m/%y-%H:%M:%S",
    )
  )
  log = app.logger


def get_log():
  return log


def get_random_string(length):
  letters_and_digits = string.ascii_lowercase
  result_str = ''.join((random.choice(letters_and_digits) for i in range(length)))
  return result_str
