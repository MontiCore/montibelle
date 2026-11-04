from flask_wtf import FlaskForm
from wtforms import BooleanField, EmailField, PasswordField, StringField
from wtforms.validators import InputRequired


class LoginForm(FlaskForm):
  username = StringField("Username", validators=[InputRequired()])
  password = PasswordField("Password", validators=[InputRequired()])
  remember = BooleanField("Remember Me")


class CreateUserForm(FlaskForm):
  username = StringField("Username", validators=[InputRequired()])
  password = PasswordField("Password", validators=[InputRequired()])
  mail = EmailField("Mail", validators=[InputRequired()])
