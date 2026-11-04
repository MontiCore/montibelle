import enum

from flask_login import UserMixin
from sqlalchemy import Enum

from extensions import db


class UserClasses(enum.Enum):
  admin = 1
  pro = 2
  user = 3


class User(db.Model, UserMixin):
  id = db.Column(db.Integer, primary_key=True)
  username = db.Column(db.String(15), unique=True)
  email = db.Column(db.String(50), unique=True)
  password = db.Column(db.String(88))
  user_class = db.Column(Enum(UserClasses))
