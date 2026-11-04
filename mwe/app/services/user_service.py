from werkzeug.security import check_password_hash, generate_password_hash

from extensions import db
from models.user import User, UserClasses


def get_password_hash(password):
  return generate_password_hash(password, method="scrypt", salt_length=8)


def create_user(username, email, password, user_class=UserClasses.user):
  hashed_password = get_password_hash(password)
  new_user = User(
    username=username,
    email=email,
    password=hashed_password,
    user_class=user_class,
  )
  db.session.add(new_user)
  db.session.commit()


def get_user(username):
  return User.query.filter_by(username=username).first()


def get_users():
  return sorted(list(User.query.all()), key=lambda u: u.id)


def delete_user(username):
  User.query.filter_by(username=username).delete()
  db.session.commit()


def is_admin(username):
  u = get_user(username)
  if u:
    return u.user_class == UserClasses.admin
  return False


def is_pro(username):
  u = get_user(username)
  if u:
    return u.user_class == UserClasses.pro
  return False


def is_pro_or_admin(username):
  return is_pro(username) or is_admin(username)


def make_admin(username):
  User.query.filter_by(username=username).update({"user_class": UserClasses.admin})
  db.session.commit()


def make_pro(username):
  User.query.filter_by(username=username).update({"user_class": UserClasses.pro})
  db.session.commit()


def change_password(username, new_password):
  User.query.filter_by(username=username).update({"password": get_password_hash(new_password)})
  db.session.commit()


def revoke_admin(username):
  User.query.filter_by(username=username).update({"user_class": UserClasses.user})
  db.session.commit()


def revoke_pro(username):
  User.query.filter_by(username=username).update({"user_class": UserClasses.user})
  db.session.commit()


def check_user(username, password_hash):
  user = User.query.filter_by(username=username).first()
  if not user:
    return False

  return check_password_hash(user.password, password_hash)
